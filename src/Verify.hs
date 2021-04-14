{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- {-# OPTIONS_GHC -Wall -Wno-unused-imports #-}

import           Language.C
import           Language.C.System.Preprocess
import           Language.C.System.GCC
import           Language.C.Data.Ident

import           Z3.Monad

import           Control.Monad.State
import           Control.Monad.Reader
import           Control.Monad.Writer

import           Data.Generics.Uniplate.Data
import           Data.Bifunctor

import           Data.Typeable
import           Data.Proxy
import           Data.Kind

import qualified Data.List as L
import qualified Data.Set as Set

import           Orphans ()
import           Ppr
import           SetExpr
import           ConstraintGen

generateUnsatCores :: Bool
generateUnsatCores = True

trackingAssert :: MonadZ3 z3 => AST -> z3 ()
trackingAssert =
  if generateUnsatCores
    then \x -> mkFreshBoolVar "track" >>= (`solverAssertAndTrack` x)
    else assert

instance MonadZ3 m => MonadZ3 (StateT a m) where
  getSolver = lift getSolver
  getContext = lift getContext

data Z3Sort = Sens_Sort | Var_Sort | Node_Sort deriving (Show, Eq)

data Z3Info =
  Z3Info
  { z3Info_setFamilyDecls :: forall (a :: [Type]). SetFamily a -> FuncDecl
  , z3Info_sensExprDecls :: SensExpr -> FuncDecl
  , z3Info_varDecls :: Int -> FuncDecl
  , z3Info_nodeDecls :: NodeId -> FuncDecl
  , z3Info_sorts :: Z3Sort -> Sort
  }

newtype Z3Converter a = Z3Converter (ReaderT Z3Info (StateT Int Z3) a)
  deriving (Functor, Applicative, Monad, MonadReader Z3Info, MonadState Int, MonadZ3, MonadIO)

defineZ3Names :: [Int] -> [NodeId] -> Z3 Z3Info
defineZ3Names vars nodeIds = do
    let makeSyms str = mapM (\x -> mkStringSymbol (str ++ show x))
        nodeIdNums = map getNodeId nodeIds

    c_exit_syms <- makeSyms "C_exit" nodeIdNums
    c_entry_syms <- makeSyms "C_entry" nodeIdNums
    s_syms <- makeSyms "S" nodeIdNums
    t_syms <- makeSyms "T" nodeIdNums

    e_syms <- makeSyms "E" nodeIdNums

    node_syms <- makeSyms "n" nodeIdNums
    var_syms <- makeSyms "v" vars
    sens_syms <- mapM mkStringSymbol ["public", "secret"]

    node_recog_syms <- makeSyms "is_n" nodeIdNums
    var_recog_syms <- makeSyms "is_v" nodeIdNums
    sens_recog_syms <- mapM mkStringSymbol ["is_public", "is_secret"]

    let buildConstructors = mapM (\(n, recog) -> mkConstructor n recog [])

    node_constructors <- buildConstructors (zip node_syms node_recog_syms)
    var_constructors <- buildConstructors (zip var_syms var_recog_syms)

    sens_constructors <- buildConstructors (zip sens_syms sens_recog_syms)

    node_type_sym <- mkStringSymbol "Node"
    var_type_sym <- mkStringSymbol "Var"
    sens_type_sym <- mkStringSymbol "Sensitivity"

    node_sort <- mkDatatype node_type_sym node_constructors
    var_sort <- mkDatatype var_type_sym var_constructors
    sens_sort <- mkDatatype sens_type_sym sens_constructors

    node_fns <- zip nodeIds <$> getDatatypeSortConstructors node_sort
    var_fns <- zip vars <$> getDatatypeSortConstructors var_sort
    [public_fn, secret_fn] <- getDatatypeSortConstructors sens_sort

    bool_sort <- mkBoolSort

    let buildFn sorts resultSort = mapM (\n -> mkFuncDecl n sorts resultSort)

    c_exit_fns <- zip nodeIds <$> buildFn [var_sort, sens_sort] bool_sort c_exit_syms
    c_entry_fns <- zip nodeIds <$> buildFn [var_sort, sens_sort] bool_sort c_entry_syms
    s_fns <- zip nodeIds <$> buildFn [node_sort, var_sort, sens_sort] bool_sort s_syms

    t_fns <- zip nodeIds <$> buildFn [] sens_sort t_syms

    e_fns <- zip nodeIds <$> buildFn [var_sort] bool_sort e_syms

    let lookup' x xs =
          case lookup x xs of
            Nothing -> error $ "defineZ3Names: Internal Z3 lookup failed: " ++ show x
            Just z -> z

    return $ Z3Info
       { z3Info_setFamilyDecls = \case
            C_Exit' n -> lookup' n c_exit_fns
            C_Entry' n -> lookup' n c_entry_fns
            Atom_S' x _y -> lookup' x s_fns
            Atom_E' x -> lookup' x e_fns

       , z3Info_sensExprDecls = \case
            SensAtom Public -> public_fn
            SensAtom Secret -> secret_fn
            Sens_T x -> lookup' x t_fns

       , z3Info_varDecls = \v -> lookup' v var_fns
       , z3Info_nodeDecls = \n -> lookup' n node_fns
       , z3Info_sorts = \case
          Sens_Sort -> sens_sort
          Var_Sort -> var_sort
          Node_Sort -> node_sort
       }

consistentSensitivity :: (Z3SetRelation a) => [NodeId] -> (NodeId -> a) -> Z3Converter AST
consistentSensitivity nodeIds f = do
  true <- mkTrue

  mkAnd =<< (forM nodeIds ( \n -> do
    (var_sort, v_sym, v) <- mkSymVar "v" Var_Sort
    (sens_sort, s_sym, s) <- mkSymVar "s" Sens_Sort
    (_, s'_sym, s') <- mkSymVar "s'" Sens_Sort

    mkForallConst [] [v_sym, s_sym, s'_sym]
      =<< join
        (mkIte <$> (z3M mkAnd [join (mkEq <$> applySetRelation (f n) [v, s] <*> pure true)
                              ,join (mkEq <$> applySetRelation (f n) [v, s'] <*> pure true)])
               <*> mkEq s s'
               <*> mkEq true true
        )))

generateS's :: [(NodeId, NodeId)] -> Z3Converter ()
generateS's [] = pure ()
generateS's sPairs@((firstPairA, firstPairB):_) = do
  true <- mkTrue

  forM_ sPairs $ \(m, n) ->
    assert =<< forallQuantifyFreeVars (Atom_S' firstPairA firstPairB) (\vars@[v,s] -> do
      (sens_sort, s'_sym, s'_var) <- mkSymVar "s'" Sens_Sort

      secret <- join $ mkApp <$> (lookupZ3FuncDecl (SensAtom Secret)) <*> pure []
      public <- join $ mkApp <$> (lookupZ3FuncDecl (SensAtom Public)) <*> pure []

      join $ mkIte <$> applySetRelation (C_Exit' n) vars
                   <*> join (mkIte <$> (z3M mkOr [applySetRelation (C_Exit' m) [v, secret], applySetRelation (C_Exit' m) [v, public]])
                                   <*> join (mkEq <$> applySetRelation (Atom_S' m n) [v, secret] <*> mkTrue)
                                   <*> join (mkEq <$> applySetRelation (Atom_S' m n) [v, s] <*> mkTrue))
                   <*> join (mkEq <$> mkTrue <*> mkTrue))

  let ms = Set.toList (Set.fromList (map fst sPairs))

  forM_ ms $ \m -> do
    let ns = map snd $ filter (\(m', n) -> m' == m) sPairs
    trackingAssert =<< consistentSensitivity ns (Atom_S' m)

generateT's :: [NodeId] -> Z3Converter ()
generateT's tNodes = do
  true <- mkTrue

  forM_ tNodes $ \n -> do
    (var_sort, v_sym, v_var) <- mkSymVar "v" Var_Sort

    (_, v'_sym, v'_var) <- mkSymVar "v'" Var_Sort

    secret <- join $ mkApp <$> (lookupZ3FuncDecl (SensAtom Secret)) <*> pure []
    public <- join $ mkApp <$> (lookupZ3FuncDecl (SensAtom Public)) <*> pure []
    sens_t <- lookupZ3FuncDecl (Sens_T n)
    n_z3 <- join $ mkApp <$> lookupZ3FuncDecl n <*> pure []

    assert =<<
      join (mkIte <$> z3M mkOr
                           [join (mkForallConst [] [v'_sym] <$> (mkNot =<< (applySetRelation (Atom_E' n) [v'_var])))
                           ,join (mkForallConst [] [v_sym] <$> (z3M mkAnd [(applySetRelation (Atom_E' n) [v_var]), (applySetRelation (C_Entry n) [v_var, public])]))
                           ]
                  <*> join (mkEq <$> (mkApp sens_t []) <*> pure public)
                  <*> join (mkEq <$> (mkApp sens_t []) <*> pure secret))

notCorrectnessCondition :: [NodeId] -> Z3Converter ()
notCorrectnessCondition nodeIds = do
  trackingAssert =<< consistentSensitivity nodeIds C_Exit'

evalZ3Converter :: [Int] -> [NodeId] -> [(NodeId, NodeId)] -> [NodeId] -> Z3Converter a -> IO (Result, Either [String] String)
evalZ3Converter vars nodeIds sPairs tNodes (Z3Converter conv) = evalZ3 $ do
  z3Info <- defineZ3Names vars nodeIds

  case (generateS's sPairs, generateT's tNodes, notCorrectnessCondition nodeIds) of
    (Z3Converter generateS's_Z3, Z3Converter generateT's_Z3, Z3Converter notCorrectnessCondition) -> do
      str <- flip evalStateT 0 $ runReaderT (generateS's_Z3 >> generateT's_Z3 >> conv >> notCorrectnessCondition >> solverToString) z3Info
      liftIO $ putStrLn str
      check
      (r, model) <- getModel
      modelOrCore <- case model of
        Nothing -> do
          core <- getUnsatCore
          Left <$> mapM astToString core
        Just m -> Right <$> showModel m
      pure (r, modelOrCore)

class Z3FuncDecl a where
  lookupZ3FuncDecl :: a -> Z3Converter FuncDecl

instance forall (t :: [Type]). Z3FuncDecl (SetFamily t) where
  lookupZ3FuncDecl x = do
    z3Info <- ask
    return $ z3Info_setFamilyDecls z3Info x

instance Z3FuncDecl SensExpr where
  lookupZ3FuncDecl = lookupZ3' z3Info_sensExprDecls

instance Z3FuncDecl Int where
  lookupZ3FuncDecl = lookupZ3' z3Info_varDecls

instance Z3FuncDecl NodeId where
  lookupZ3FuncDecl = lookupZ3' z3Info_nodeDecls

lookupZ3' :: (Z3Info -> (a -> r)) -> a -> Z3Converter r
lookupZ3' accessor x = do
  f <- fmap accessor ask
  return $ f x

lookupZ3Sort :: Z3Sort -> Z3Converter Sort
lookupZ3Sort = lookupZ3' z3Info_sorts

mkAppM :: MonadZ3 z3 => FuncDecl -> [z3 AST] -> z3 AST
mkAppM decl = z3M (mkApp decl)

z3M :: MonadZ3 z3 => ([a] -> z3 b) -> [z3 a] -> z3 b
z3M f argsM =
  f =<< sequence argsM

lookupSetFamilyFn :: SetFamily a -> Z3Converter (FuncDecl, [AST])
lookupSetFamilyFn sf@(C_Exit' _n) = do
  f <- lookupZ3FuncDecl sf
  pure (f, [])

lookupSetFamilyFn sf@(C_Entry' _n) = do
  f <- lookupZ3FuncDecl sf
  pure (f, [])

lookupSetFamilyFn sf@(Atom_S' _x y) = do
  f <- lookupZ3FuncDecl sf
  (f,) <$> sequence [toZ3 y]

lookupSetFamilyFn sf@(Atom_E' _x) = do
  f <- lookupZ3FuncDecl sf
  pure (f, [])

applyFamilyFnM :: SetFamily a -> [Z3Converter AST] -> Z3Converter AST
applyFamilyFnM sf0 restArgs = do
  (sf, args) <- lookupSetFamilyFn sf0
  mkAppM sf (map pure args ++ restArgs)

class FreeVars (a :: [Type]) where
  freeVars :: f a -> Z3Converter [(Sort, App, AST)]

-- NOTE: We do not worry about name collisions since there should be no
-- nested foralls currently. If there is a nested forall, this will need to
-- be revisited (with freshness of names ensured explicitly)
instance FreeVars '[] where
  freeVars _ = pure []

instance FreeVars xs => FreeVars (Var : xs) where
  freeVars _ = (:) <$> mkSymVar "v" Var_Sort <*> freeVars (Proxy @xs)

instance FreeVars xs => FreeVars (SensExpr : xs) where
  freeVars _ = (:) <$> mkSymVar "s" Sens_Sort <*> freeVars (Proxy @xs)

class FreeVarsE f where
  freeVarsE :: f a -> Z3Converter [(Sort, App, AST)]

instance FreeVarsE SetFamily where
  freeVarsE e@(C_Exit' {}) = freeVars e
  freeVarsE e@(C_Entry' {}) = freeVars e
  freeVarsE e@(Atom_S' {}) = freeVars e
  freeVarsE e@(Atom_E' {}) = freeVars e

instance FreeVarsE AtomicSet where
  freeVarsE (SetFamily x) = freeVarsE x
  freeVarsE e@(SingleVar {}) = freeVarsE e

instance FreeVarsE SetExpr where
  freeVarsE (SE_Atom x) = freeVarsE x
  freeVarsE (SE_Union x y) = L.union <$> freeVarsE x <*> freeVarsE y
  freeVarsE (SE_UnionSingle x _ _) = freeVarsE x
  freeVarsE (SE_IfThenElse _ x y) = L.union <$> freeVarsE x <*> freeVarsE y
  freeVarsE SE_Empty = pure []

class Z3SetRelation a where
  applySetRelation :: a -> [AST] -> Z3Converter AST

  applySetRelationM :: a -> [Z3Converter AST] -> Z3Converter AST
  applySetRelationM sr xs = applySetRelation sr =<< sequence xs

instance Z3SetRelation (SetFamily a) where
  applySetRelation sr = applyFamilyFnM sr . map pure
  applySetRelationM = applyFamilyFnM

instance Z3SetRelation (AtomicSet a) where
  applySetRelation (SetFamily sr) args = applySetRelation sr args
  applySetRelation (SingleVar i) _ = toZ3 i

instance Z3SetRelation (SetExpr a) where
  applySetRelation (SE_Atom sr) args = applySetRelation sr args

  applySetRelation (SE_Union x y) args = do
    z3M mkOr [applySetRelation x args, applySetRelation y args]

  applySetRelation (SE_UnionSingle x v s) args@[v',s'] = do
    z3_v <- toZ3 v
    z3_s <- toZ3 s

    z3M mkOr [ applySetRelation x args
             , z3M mkAnd [mkEq z3_v v', mkEq z3_s s']
             ]
    -- applySetRelationM x [toZ3 v, toZ3 s]

  applySetRelation (SE_IfThenElse (SensEqual sensX sensY) t f) args = do
    z3_sensX <- toZ3 sensX
    z3_sensY <- toZ3 sensY

    eql <- mkEq z3_sensX z3_sensY

    join $ mkIte eql <$> applySetRelation t args <*> applySetRelation f args

  applySetRelation (SE_IfThenElse (PairIn (v, s) x) t f) args = do
    z3_v <- toZ3 v
    z3_s <- toZ3 s

    cond <- applySetRelation x [z3_v, z3_s]

    join $ mkIte cond <$> applySetRelation t args <*> applySetRelation f args

  applySetRelation SE_Empty _args = error "applySetRelation: SE_Empty"


forallQuantifyFreeVars :: forall f a. (FreeVarsE f) => f a -> ([AST] -> Z3Converter AST) -> Z3Converter AST
forallQuantifyFreeVars e k = do
  fvs <- freeVarsE e

  let sorts = map (\(x, _, _) -> x) fvs
      syms = map (\(_, x, _) -> x) fvs
      vars = map (\(_, _, x) -> x) fvs

  mkForallConst [] syms =<< k vars

class ToZ3 a where
  toZ3 :: a -> Z3Converter AST


mkSymVar :: String -> Z3Sort -> Z3Converter (Sort, App, AST)
mkSymVar name z3sort = do
  uniq <- get
  modify succ

  sort <- lookupZ3Sort z3sort

  var <- mkFreshVar name sort
  app <- toApp var
  return (sort, app, var)

instance ToZ3 NodeId where
  toZ3 n = join $ mkApp <$> lookupZ3FuncDecl n <*> pure []

instance ToZ3 Int where
  toZ3 n = join $ mkApp <$> lookupZ3FuncDecl n <*> pure []

instance ToZ3 Sensitivity where
  toZ3 = toZ3 . SensAtom

instance ToZ3 SensExpr where
  toZ3 s@(SensAtom _) =
    join $ mkApp <$> (lookupZ3FuncDecl s) <*> pure []

  toZ3 s@(Sens_T x) = do
    z3_t <- lookupZ3FuncDecl s
    mkAppM z3_t []


instance ToZ3 SetConstraint where
  toZ3 (lhs :=: SE_Empty) = do
    forallQuantifyFreeVars lhs $ \vars -> do
      join $ mkEq <$> applySetRelation lhs vars <*> mkFalse

  toZ3 (lhs@(Atom_E' _) :=: SE_Atom (SingleVar v)) = do
    z3_v <- (`mkApp` []) =<< lookupZ3FuncDecl v

    join $ mkEq <$> applySetRelation lhs [z3_v] <*> mkTrue

  toZ3 (lhs@(Atom_E' _) :=: SE_Atom (SetFamily x)) =
    forallQuantifyFreeVars lhs $ \vars ->
      join (mkEq <$> applySetRelation lhs vars <*> applySetRelation x vars)

  toZ3 (lhs@(Atom_E' _) :=: SE_UnionSingle {}) = error "Assignment of E to a singleton of a variable/sensitivity pair"

  toZ3 (lhs@(Atom_E' _) :=: SE_Union x y) =
    forallQuantifyFreeVars lhs $ \vars -> do
      the_or <- z3M mkOr [applySetRelation x vars, applySetRelation y vars]
      join (mkEq <$> applySetRelation lhs vars <*> pure the_or)



  toZ3 (lhs :=: SE_Atom (SetFamily x)) =
    forallQuantifyFreeVars lhs $ \vars ->
      join (mkEq <$> applySetRelation lhs vars <*> applySetRelation x vars)

  toZ3 (_ :=: SE_Atom (SingleVar _)) = error "Assignment of a set family other than E to a singleton containing a variable (not a pair)"

  toZ3 (lhs :=: SE_Union x y) =
    forallQuantifyFreeVars lhs $ \vars -> do
      the_or <- z3M mkOr [applySetRelation x vars, applySetRelation y vars]
      join (mkEq <$> applySetRelation lhs vars <*> pure the_or)

  toZ3 (lhs :=: SE_UnionSingle x v0 s0) = do

    (varSort, v_sym, v_var) <- mkSymVar "v" Var_Sort
    (sensSort, s_sym, s_var) <- mkSymVar "s" Sens_Sort
    let vs = [v_var, s_var]

    mkForallConst [] [v_sym, s_sym]
      =<< join (mkIte <$> z3M mkAnd [join (mkEq v_var <$> toZ3 v0), join (mkEq s_var <$> toZ3 s0)]
                      <*> join (mkEq <$> applySetRelation lhs vs <*> mkTrue)
                      <*> join (mkEq <$> applySetRelation lhs vs <*> applySetRelation x vs))

  toZ3 (lhs :=: SE_IfThenElse (SensEqual sensX sensY) t f) = do
    (varSort, v_sym, v_var) <- mkSymVar "v" Var_Sort
    (sensSort, s_sym, s_var) <- mkSymVar "s" Sens_Sort
    let vs = [v_var, s_var]

    z3_sensX <- toZ3 sensX
    z3_sensY <- toZ3 sensY

    eql <- mkEq z3_sensX z3_sensY

    z3_t <- applySetRelation t vs
    z3_f <- applySetRelation f vs

    mkForallConst [] [v_sym, s_sym]
      =<< join (mkIte eql <$> join (mkEq <$> applySetRelation lhs vs <*> pure z3_t) <*> join (mkEq <$> applySetRelation lhs vs <*> pure z3_f))

  toZ3 (lhs :=: SE_IfThenElse (PairIn (v, s) x) t f) = do

    z3_v <- toZ3 v
    z3_s <- toZ3 s
    
    cond <- applySetRelation x [z3_v, z3_s]

    (varSort, v_sym, v_var) <- mkSymVar "v" Var_Sort
    (sensSort, s_sym, s_var) <- mkSymVar "s" Sens_Sort
    let vs = [v_var, s_var]

    z3_t <- applySetRelation t vs
    z3_f <- applySetRelation f vs

    mkForallConst [] [v_sym, s_sym]
      =<< join (mkIte cond <$> join (mkEq <$> applySetRelation lhs vs <*> pure z3_t) <*> join (mkEq <$> applySetRelation lhs vs <*> pure z3_f))

constraintsToZ3 :: SetConstraints -> Z3Converter ()
constraintsToZ3 cs = do
  asts <- mapM toZ3 cs

  let astsZipped = zip asts [0..]

  forM_ astsZipped $ \(ast, n) -> do
    track <- mkFreshBoolVar $ "ast" ++ show n

    {- trackingAssert track -}
    assert ast

nodeIdToLoc :: CTranslationUnit (NodeInfo, NodeId) -> NodeId -> (NodeId, Maybe Position)
nodeIdToLoc transUnit nodeId =
  (nodeId, fmap posOf . lookup nodeId $ foldMap (\(info, nodeId') -> [(nodeId', info)]) transUnit)

nodeIdLocInfo :: [(NodeId, Maybe Position)] -> String
nodeIdLocInfo = unlines . map go
  where
    go (nodeId, pos_maybe) = ppr nodeId ++ ": " ++
      case pos_maybe of
        Nothing -> "<no position info>"
        Just pos -> show pos

getAnns :: CTranslationUnit a -> [a]
getAnns = foldMap (:[])

gccPath :: FilePath
gccPath = "/usr/bin/gcc"

main :: IO ()
main = do
  let fileName = "../test.c"

  let gcc = newGCC gccPath

  stream_either <- runPreprocessor gcc $ CppArgs
    { cppOptions = []
    , extraOptions = []
    , cppTmpDir = Nothing
    , inputFile = fileName
    , outputFile = Nothing
    }

  case stream_either of
    Left err -> putStrLn $ "Preprocessing failed: " ++ show err
    Right stream -> do
      case parseC stream (initPos fileName) of
        Left err -> error (show err)
        Right parsed -> do
          let parsed' = flip runState (NodeId 0) $ traverse (\x -> (x,) <$> newNodeId) parsed
              parsed'' = first (fmap snd) parsed'
              constraints = execConstraintGen $ transformM (constAction handleTransUnit) parsed''
              nodeLocs = map (nodeIdToLoc (fst parsed')) (getAnns (fst parsed''))
              theNodeIds = getNodeIds constraints

          putStrLn $ ppr constraints

          -- putStrLn (nodeIdLocInfo nodeLocs)
          print parsed'

          let tPairs = getTNodes constraints
              sPairs = getSPairs constraints
          -- let sPairs = tPairs `Set.union` getSPairs constraints

          print sPairs
          print tPairs

          (r, modelStr_maybe) <- evalZ3Converter (Set.toList (getVars constraints))
                                                 (Set.toList theNodeIds)
                                                 (Set.toList sPairs)
                                                 (Set.toList tPairs)
                                                 (constraintsToZ3 constraints)
          print r

          case modelStr_maybe of
            Left core -> putStrLn $ "Unsat core:\n" <> unlines core
            Right modelStr -> do
              putStrLn $ "Model:\n" <> modelStr

