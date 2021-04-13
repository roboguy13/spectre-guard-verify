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

{-# OPTIONS_GHC -Wall -Wno-unused-imports #-}

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

    t_fns <- zip nodeIds <$> buildFn [node_sort] sens_sort t_syms

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
            Sens_T x _y -> lookup' x t_fns

       , z3Info_varDecls = \v -> lookup' v var_fns
       , z3Info_nodeDecls = \n -> lookup' n node_fns
       , z3Info_sorts = \case
          Sens_Sort -> sens_sort
          Var_Sort -> var_sort
          Node_Sort -> node_sort
       }

generateS's :: [(NodeId, NodeId)] -> Z3Converter ()
generateS's [] = pure ()
generateS's sPairs@((firstPairA, firstPairB):_) = do
  true <- mkTrue

  forM_ sPairs $ \(m, n) ->
    assert =<< forallQuantifyFreeVars (Atom_S' firstPairA firstPairB) (\vars@[v,s] -> do
      (sens_sort, s'_sym, s'_var) <- mkSymVar "s'" Sens_Sort

      secret <- join $ mkApp <$> (lookupZ3FuncDecl (SensAtom Secret)) <*> pure []

      join $ mkIte <$> applySetRelation (C_Exit' n) vars
        <*> join (mkIte <$> (mkExists [] [s'_sym] [sens_sort]
                              =<< applySetRelation (C_Exit' m) [v, s'_var]
                            )
                        <*> applySetRelation (Atom_S' m n) [v, secret]
                        <*> applySetRelation (Atom_S' m n) [v, s]
                 )
        <*> mkEq true true)

generateT's :: [(NodeId, NodeId)] -> Z3Converter ()
generateT's tPairs = do
  true <- mkTrue

  forM_ tPairs $ \(m, n) -> do
    (sens_sort, s_sym, s_var) <- mkSymVar "s" Sens_Sort
    (var_sort, v_sym, v_var) <- mkSymVar "v" Var_Sort

    secret <- join $ mkApp <$> (lookupZ3FuncDecl (SensAtom Secret)) <*> pure []
    public <- join $ mkApp <$> (lookupZ3FuncDecl (SensAtom Public)) <*> pure []
    sens_t <- lookupZ3FuncDecl (Sens_T m n)
    n_z3 <- join $ mkApp <$> lookupZ3FuncDecl n <*> pure []

    assert =<< mkForall [] [v_sym] [var_sort]
      =<< join
        (mkIte <$> (mkExists [] [s_sym] [sens_sort]
                     =<< (z3M mkAnd [mkEq s_var secret, applySetRelation (Atom_S' m n) [v_var, s_var]]))
               <*> join (mkEq <$> (mkApp sens_t [n_z3]) <*> pure secret)
               <*> join (mkEq <$> (mkApp sens_t [n_z3]) <*> pure public)
        )

notCorrectnessCondition :: [NodeId] -> Z3Converter ()
notCorrectnessCondition nodeIds = do
  -- (node_sort, n_sym, n) <- mkSymVar "n" Node_Sort

  true <- mkTrue

  secret <- join $ mkApp <$> (lookupZ3FuncDecl (SensAtom Secret)) <*> pure []
  public <- join $ mkApp <$> (lookupZ3FuncDecl (SensAtom Public)) <*> pure []

  forM_ nodeIds $ \n -> do
    (var_sort, v_sym, v) <- mkSymVar "v" Var_Sort
    (sens_sort, s_sym, s) <- mkSymVar "s" Sens_Sort
    (_, s'_sym, s') <- mkSymVar "s'" Sens_Sort


    assert =<< mkNot =<<
      mkForall [] [v_sym, s_sym, s'_sym] [var_sort, sens_sort, sens_sort]
        =<< join
          (mkIte <$> (z3M mkAnd [join (mkEq <$> applySetRelation (C_Exit' n) [v, s] <*> pure true)
                                ,join (mkEq <$> applySetRelation (C_Exit' n) [v, s'] <*> pure true)])
                 <*> mkEq s s'
                 <*> mkEq true true
          )

-- maybeMap :: (a -> b)

evalZ3Converter :: [Int] -> [NodeId] -> [(NodeId, NodeId)] -> [(NodeId, NodeId)] -> Z3Converter a -> IO (Result, Maybe String)
evalZ3Converter vars nodeIds sPairs tPairs (Z3Converter conv) = evalZ3 $ do
  z3Info <- defineZ3Names vars nodeIds

  case (generateS's sPairs, generateT's tPairs, notCorrectnessCondition nodeIds) of
    (Z3Converter generateS's_Z3, Z3Converter generateT's_Z3, Z3Converter notCorrectnessCondition) -> do
      str <- flip evalStateT 0 $ runReaderT (generateS's_Z3 >> generateT's_Z3 >> conv >> notCorrectnessCondition >> solverToString) z3Info
      liftIO $ putStrLn str
      check
      (r, model) <- getModel
      modelStr <- case model of
        Nothing -> pure Nothing
        Just m -> Just <$> showModel m
      pure (r, modelStr)

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
  freeVars :: f a -> Z3Converter [(Sort, Symbol, AST)]

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
  freeVarsE :: f a -> Z3Converter [(Sort, Symbol, AST)]

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

  applySetRelation (SE_UnionSingle x v s) _args =
    applySetRelationM x [toZ3 v, toZ3 s]

  applySetRelation (SE_IfThenElse (sensX, sensY) t f) args = do
    z3_sensX <- toZ3 sensX
    z3_sensY <- toZ3 sensY

    eql <- mkEq z3_sensX z3_sensY

    join $ mkIte eql <$> applySetRelation t args <*> applySetRelation f args

  applySetRelation SE_Empty _args = error "applySetRelation: SE_Empty"


forallQuantifyFreeVars :: forall f a. (FreeVarsE f) => f a -> ([AST] -> Z3Converter AST) -> Z3Converter AST
forallQuantifyFreeVars e k = do
  fvs <- freeVarsE e

  let sorts = map (\(x, _, _) -> x) fvs
      syms = map (\(_, x, _) -> x) fvs
      vars = map (\(_, _, x) -> x) fvs

  mkForall [] syms sorts =<< k vars

class ToZ3 a where
  toZ3 :: a -> Z3Converter AST


mkSymVar :: String -> Z3Sort -> Z3Converter (Sort, Symbol, AST)
mkSymVar name z3sort = do
  uniq <- get
  modify succ

  sort <- lookupZ3Sort z3sort
  sym <- mkStringSymbol (name ++ "__" ++ show uniq)

  var <- mkVar sym sort
  return (sort, sym, var)

-- mkFreshVarWith :: Z3Sort -> Z3Converter (Sort, Symbol, AST)
-- mkFreshVarWith z3sort = do
--   sort <- lookupZ3Sort z3sort


instance ToZ3 NodeId where
  toZ3 n = join $ mkApp <$> lookupZ3FuncDecl n <*> pure []

instance ToZ3 Int where
  toZ3 n = join $ mkApp <$> lookupZ3FuncDecl n <*> pure []

instance ToZ3 SensExpr where
  toZ3 s@(SensAtom _) =
    join $ mkApp <$> (lookupZ3FuncDecl s) <*> pure []

  toZ3 s@(Sens_T x y) = do
    z3_t <- lookupZ3FuncDecl s
    mkAppM z3_t [toZ3 y]


instance ToZ3 SetConstraint where
  toZ3 (lhs :=: SE_Empty) = do
    forallQuantifyFreeVars lhs $ \vars -> do
      mkNot =<< applySetRelation lhs vars

  toZ3 (lhs@(Atom_E' _) :=: SE_Atom (SingleVar v)) = do
    z3_v <- (`mkApp` []) =<< lookupZ3FuncDecl v
    applySetRelation lhs [z3_v]

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

    -- (varSort, v_sym, v_var) <- mkSymVar "v" Var_Sort
    -- (sensSort, s_sym, s_var) <- mkSymVar "s" Sens_Sort

    -- mkForall [] [v_sym, s_sym] [ varSort, sensSort ]
    --   =<< join (mkEq <$> applyFamilyFnM lhs [pure v_var, pure s_var] <*> applyFamilyFnM x [pure v_var, pure s_var])

  toZ3 (_ :=: SE_Atom (SingleVar _)) = error "Assignment of a set family other than E to a singleton containing a variable (not a pair)"

  toZ3 (lhs :=: SE_Union x y) =
    forallQuantifyFreeVars lhs $ \vars -> do
      the_or <- z3M mkOr [applySetRelation x vars, applySetRelation y vars]
      join (mkEq <$> applySetRelation lhs vars <*> pure the_or)
    -- (varSort, v_sym, v_var) <- mkSymVar "v" Var_Sort
    -- (sensSort, s_sym, s_var) <- mkSymVar "s" Sens_Sort
    -- let vs = [v_var, s_var]

    -- the_or <- z3M mkOr [applySetRelation x vs, applySetRelation y vs]

    -- mkForall [] [v_sym, s_sym] [ varSort, sensSort ]
    --   =<< join (mkEq <$> applySetRelation lhs vs <*> pure the_or)

  toZ3 (lhs :=: SE_UnionSingle x v0 s0) = do
    -- forallQuantifyFreeVars lhs $ \vars -> do
    --   z3M mkOr [join $ mkEq <$> applySetRelation lhs vs <*> applySetRelation x vs
    --                      ,z3M mkAnd [join (mkEq v_var <$> toZ3 v0)
    --                                 ,join (mkEq s_var <$> toZ3 s0)
    --                                 ]
    --                      ]

    (varSort, v_sym, v_var) <- mkSymVar "v" Var_Sort
    (sensSort, s_sym, s_var) <- mkSymVar "s" Sens_Sort
    let vs = [v_var, s_var]

    mkForall [] [v_sym, s_sym] [ varSort, sensSort ]
      =<< (z3M mkOr [join $ mkEq <$> applySetRelation lhs vs <*> applySetRelation x vs
                         ,z3M mkAnd [join (mkEq v_var <$> toZ3 v0)
                                    ,join (mkEq s_var <$> toZ3 s0)
                                    ]
                         ])


  toZ3 (lhs :=: SE_IfThenElse (sensX, sensY) t f) = do
    (varSort, v_sym, v_var) <- mkSymVar "v" Var_Sort
    (sensSort, s_sym, s_var) <- mkSymVar "s" Sens_Sort
    let vs = [v_var, s_var]

    z3_sensX <- toZ3 sensX
    z3_sensY <- toZ3 sensY

    eql <- mkEq z3_sensX z3_sensY

    z3_t <- applySetRelation t vs
    z3_f <- applySetRelation f vs

    mkForall [] [v_sym, s_sym] [ varSort, sensSort ]
      =<< join (mkIte eql <$> join (mkEq <$> applySetRelation lhs vs <*> pure z3_t) <*> join (mkEq <$> applySetRelation lhs vs <*> pure z3_f))



constraintsToZ3 :: SetConstraints -> Z3Converter ()
constraintsToZ3 cs = do
  asts <- mapM toZ3 cs
  mapM_ assert asts

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

          putStrLn $ ppr constraints
          -- putStrLn (nodeIdLocInfo nodeLocs)
          -- print parsed'

          (r, modelStr_maybe) <- evalZ3Converter (Set.toList (getVars constraints))
                                                 (Set.toList (getNodeIds constraints))
                                                 (Set.toList (getSPairs constraints))
                                                 (Set.toList (getTPairs constraints))
                                                 (constraintsToZ3 constraints)
          print r

          case modelStr_maybe of
            Nothing -> putStrLn "No model generated"
            Just modelStr -> do
              putStrLn $ "Model:\n" <> modelStr

