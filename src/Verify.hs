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
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}

-- {-# OPTIONS_GHC -Wall -Wno-unused-imports #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

import           Language.C
import           Language.C.System.Preprocess
import           Language.C.System.GCC
import           Language.C.Data.Ident

import           System.FilePath.Posix
import           System.Process
import           System.IO

import           Z3.Monad

import           Control.Monad.State
import           Control.Monad.Reader
import           Control.Monad.Writer

import           Data.Generics.Uniplate.Data
import           Data.Bifunctor

import           Data.Typeable
import           Data.Proxy
import           Data.Kind
import           Data.Constraint

import qualified Data.ByteString as BS

import           Data.Maybe (maybeToList)

import qualified Data.List as L
import qualified Data.Set as Set

import           Orphans ()
import           Ppr
import           SetExpr
import           Pattern
import           ConstraintGen
-- import           DOT

-- data Z3Var a = Z3Var { getZ3Var :: AST }

data Z3Var a where
  Z3VarSens :: (App, AST) -> Z3Var SensExpr
  Z3VarVar :: (App, AST) -> Z3Var Var
  Z3VarPair :: (App, AST) -> (App, AST) -> Z3Var (a, b)

infixl 4 <!>
(<!>) :: Monad m => m (a -> m b) -> m a -> m b
f <!> x = join (f <*> x)

mkSymVar :: String -> Z3Sort -> Z3Converter (Sort, App, AST)
mkSymVar name z3sort = do
  uniq <- get
  modify succ

  sort <- lookupZ3Sort z3sort

  var <- mkFreshVar name sort
  app <- toApp var
  return (sort, app, var)

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
  { z3Info_setFamilyDecls :: forall a. AnalysisSetFamily a -> FuncDecl
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
            C_Exit n -> lookup' n c_exit_fns
            C_Entry n -> lookup' n c_entry_fns
            S x _y -> lookup' x s_fns
            -- E x -> lookup' x e_fns

       , z3Info_sensExprDecls = \case
            SensAtom Public -> public_fn
            SensAtom Secret -> secret_fn
            SensFamily (SensT x) -> lookup' x t_fns

       , z3Info_varDecls = \v -> lookup' v var_fns
       , z3Info_nodeDecls = \n -> lookup' n node_fns
       , z3Info_sorts = \case
          Sens_Sort -> sens_sort
          Var_Sort -> var_sort
          Node_Sort -> node_sort
       }

-- consistentSensitivity :: (Z3SetRelation a) => [NodeId] -> (NodeId -> a) -> Z3Converter [AST]
-- consistentSensitivity nodeIds f = do
--   true <- mkTrue

--   (forM nodeIds ( \n -> do
--     (var_sort, v_sym, v) <- mkSymVar "v" Var_Sort
--     (sens_sort, s_sym, s) <- mkSymVar "s" Sens_Sort
--     (_, s'_sym, s') <- mkSymVar "s'" Sens_Sort

--     mkForallConst [] [v_sym, s_sym, s'_sym]
--       =<<
--         (mkIte <$> (z3M mkAnd [mkEq <$> applySetRelation (f n) [v, s]  <!> pure true
--                               ,mkEq <$> applySetRelation (f n) [v, s'] <!> pure true])
--                <*> mkEq s s'
--                <!> mkEq true true
--         )))

-- generateSConstraints :: [(NodeId, NodeId)] -> [SetConstraint]
-- generateSConstraints = map go
--   where
--     go (m, n) =
--       let sf :: AnalysisSetFamily '[Var, SensExpr]
--           sf = atom_s m n

--           comp :: SetComprehension (Var, SensExpr)
--           comp =
--             SetComp'
--               (PairPat :-> \(v, s) ->
--                   let s' = undefined
--                   in
--                   SE_UnionSingle SE_Empty v s')
--               (PairPat :-> (`CompPred_PairIn` c_exit n))
--       in
--       sf `SetConstr` SE_Comp comp

generateS's :: [(NodeId, NodeId)] -> Z3Converter ()
generateS's [] = pure ()
generateS's sPairs@((firstPairA, firstPairB):_) = undefined
  -- true <- mkTrue

  -- forM_ sPairs $ \(m, n) ->
  --   -- let rhs = 
  --   -- in
  --   -- undefined
  --   assert =<< forallQuantifyFreeVars (s_family firstPairA firstPairB) (\vars@[v,s] -> do
  --     secret <- mkApp <$> (lookupZ3FuncDecl (SensAtom Secret)) <!> pure []
  --     public <- mkApp <$> (lookupZ3FuncDecl (SensAtom Public)) <!> pure []

  --     mkIte <$> applySetRelation (C_Entry n) vars
  --                  <*> (mkIte <$> z3M mkOr [applySetRelation (C_Entry n) [v, public], applySetRelation (C_Entry n) [v, secret]]
  --                             <*> (mkEq <$> applySetRelation (s_family m n) [v, secret] <!> mkTrue)
  --                             <!> (mkEq <$> applySetRelation (s_family m n) [v, s] <!> mkTrue))
  --                  <!> (mkEq <$> mkTrue <!> mkTrue))

  -- let ms = Set.toList (Set.fromList (map fst sPairs))

  -- forM_ ms $ \m -> do
  --   let ns = map snd $ filter (\(m', n) -> m' == m) sPairs
  --   trackingAssert =<< mkAnd =<< (consistentSensitivity ns (s_family m))

generateT's :: [NodeId] -> Z3Converter ()
generateT's tNodes = undefined
  -- true <- mkTrue

  -- forM_ tNodes $ \n -> do
  --   (var_sort, v_sym, v_var) <- mkSymVar "v" Var_Sort

  --   (_, v'_sym, v'_var) <- mkSymVar "v'" Var_Sort

  --   secret <- mkApp <$> (lookupZ3FuncDecl (SensAtom Secret)) <!> pure []
  --   public <- mkApp <$> (lookupZ3FuncDecl (SensAtom Public)) <!> pure []
  --   sens_t <- lookupZ3FuncDecl (SensT n)
  --   n_z3 <- mkApp <$> lookupZ3FuncDecl n <!> pure []

  --   assert =<<
  --     mkIte <$> z3M mkOr
  --                    [mkForallConst [] [v'_sym] =<< (mkNot =<< (applySetRelation (Atom_E' n) [v'_var]))
  --                    ,mkForallConst [] [v_sym] =<< (mkImplies <$> (applySetRelation (Atom_E' n) [v_var]) <!> (applySetRelation (C_Entry n) [v_var, public]))
  --                    ]
  --           <*> (mkEq <$> (mkApp sens_t []) <!> pure public)
  --           <!> (mkEq <$> (mkApp sens_t []) <!> pure secret)

correctnessCondition :: [NodeId] -> Z3Converter ()
correctnessCondition nodeIds = undefined
  -- asts <- consistentSensitivity nodeIds C_Exit
  -- mapM_ trackingAssert asts

evalZ3Converter :: [Int] -> [NodeId] -> [(NodeId, NodeId)] -> [NodeId] -> Z3Converter a -> IO (Result, Either [String] String)
evalZ3Converter vars nodeIds sPairs tNodes (Z3Converter conv) = evalZ3 $ do
  params <- mkParams
  paramsSetBool params <$> mkStringSymbol "core.minimize" <!> pure True
  solverSetParams params

  z3Info <- defineZ3Names vars nodeIds

  case (generateS's sPairs, generateT's tNodes, correctnessCondition nodeIds) of
    (Z3Converter generateS's_Z3, Z3Converter generateT's_Z3, Z3Converter correctnessCondition) -> do
      str <- flip evalStateT 0 $ runReaderT (generateS's_Z3 >> generateT's_Z3 >> conv >> correctnessCondition >> solverToString) z3Info
      -- liftIO $ hPutStrLn stderr str
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

instance forall t. Z3FuncDecl (AnalysisSetFamily t) where
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

lookupSetFamilyFn :: AnalysisSetFamily a -> Z3Converter (FuncDecl, [AST])
lookupSetFamilyFn sf@(C_Exit _n) = do
  f <- lookupZ3FuncDecl sf
  pure (f, [])

lookupSetFamilyFn sf@(C_Entry _n) = do
  f <- lookupZ3FuncDecl sf
  pure (f, [])

lookupSetFamilyFn sf@(S _x y) = do
  f <- lookupZ3FuncDecl sf
  (f,) <$> sequence [toZ3 y]

applyFamilyFn :: AnalysisSetFamily a -> [AST] -> Z3Converter AST
applyFamilyFn sf0 restArgs = do
  (sf, args) <- lookupSetFamilyFn sf0
  mkApp sf (args ++ restArgs)

class BaseVar a where
  baseVarPrefix_Sort :: proxy a -> (String, Z3Sort)

instance BaseVar SensExpr where
  baseVarPrefix_Sort _ = ("s", Sens_Sort)

instance BaseVar Var where
  baseVarPrefix_Sort _ = ("v", Var_Sort)

class FreeVars a where
  freeVars :: f a -> Z3Converter [(Sort, App, AST)]
  mkZ3Var :: Z3Converter (Z3Var a)

lamRepr :: FreeVars a => Lam (a -> b) -> Z3Converter (Z3Var a)
lamRepr _ = mkZ3Var

-- instance FreeVars a => Repr Z3Var a where
--   type ReprM Z3Var a = Z3Converter
--   repr = mkZ3Var

mkSymVar' :: (String, Z3Sort) -> Z3Converter (App, AST)
mkSymVar' p = do
  (_, y, z) <- uncurry mkSymVar p
  return (y, z)

instance (BaseVar a, BaseVar b, FreeVars a, FreeVars b) => FreeVars (a, b) where
  freeVars _ = (<>) <$> freeVars (Proxy @a) <*> freeVars (Proxy @b)
  mkZ3Var = Z3VarPair <$> mkSymVar' (baseVarPrefix_Sort @a Proxy)
                      <*> mkSymVar' (baseVarPrefix_Sort @b Proxy)

instance FreeVars SensExpr where
  freeVars _ = do
    x <- mkSymVar "s" Sens_Sort
    return [x]
  mkZ3Var = Z3VarSens <$> mkSymVar' ("s", Sens_Sort)

instance FreeVars Var where
  freeVars _ = do
    x <- mkSymVar "v" Var_Sort
    return [x]
  mkZ3Var = Z3VarVar <$> mkSymVar' ("v", Var_Sort)

forallQuantifyFreeVars :: forall f a. (FreeVars a) => f a -> (Z3Var a -> Z3Converter AST) -> Z3Converter AST
forallQuantifyFreeVars e k = do
  z3Var <- mkZ3Var @a
  mkForallConst [] (getZ3VarApps z3Var) =<< k z3Var

forallQuantifyZ3Var :: forall f a. (FreeVars a) => Z3Var a -> Z3Converter AST -> Z3Converter AST
forallQuantifyZ3Var z3Var m = do
  mkForallConst [] (getZ3VarApps z3Var) =<< m

class Z3Equality a b where
  z3Eq :: a -> b -> Z3Converter AST

instance Z3Equality AST AST where
  z3Eq = mkEq

instance (Z3Equality a a, Z3Equality b b) => Z3Equality (a, b) (a, b) where
  z3Eq (x, y) (x', y') =
    z3M mkAnd [z3Eq x x', z3Eq y y']

instance Z3Equality (Z3Var a) (Z3Var a) where
  z3Eq (Z3VarSens (_, x)) (Z3VarSens (_, y)) = mkEq x y
  z3Eq (Z3VarVar (_, x)) (Z3VarVar (_, y)) = mkEq x y
  z3Eq (Z3VarPair (_, x) (_, y)) (Z3VarPair (_, x') (_, y')) = z3Eq (x, y) (x', y')

instance (ToZ3 a, ToZ3 b) => Z3Equality (Z3Var (a, b)) (a, b) where
  z3Eq (Z3VarPair x y) (x', y') = do
    x'_z3 <- toZ3 x'
    y'_z3 <- toZ3 y'
    z3Eq (snd x, snd y) (x'_z3, y'_z3)

getZ3VarASTs :: Z3Var a -> [AST]
getZ3VarASTs (Z3VarSens x) = [snd x]
getZ3VarASTs (Z3VarVar x) = [snd x]
getZ3VarASTs (Z3VarPair x y) = [snd x, snd y]

getZ3VarApps :: Z3Var a -> [App]
getZ3VarApps (Z3VarSens x) = [fst x]
getZ3VarApps (Z3VarVar x) = [fst x]
getZ3VarApps (Z3VarPair x y) = [fst x, fst y]

class Z3SetRelation f where
  applySetRelation :: f a -> Z3Var a -> Z3Converter AST

instance Z3SetRelation AnalysisSetFamily where
  applySetRelation sf args = applyFamilyFn sf (getZ3VarASTs args)

-- class Z3SetRelation a where
--   applySetRelation :: a -> [AST] -> Z3Converter AST

--   applySetRelationM :: a -> [Z3Converter AST] -> Z3Converter AST
--   applySetRelationM sr xs = applySetRelation sr =<< sequence xs

-- instance Z3SetRelation (AnalysisSetFamily a) where
--   applySetRelation sr = applyFamilyFnM sr . map pure
--   applySetRelationM = applyFamilyFnM

-- -- instance Z3SetRelation (AtomicSet a) where
-- --   applySetRelation (AnalysisSetFamily sr) args = applySetRelation sr args
-- --   applySetRelation (SingleVar i) _ = toZ3 i

-- instance Z3SetRelation (SetExpr AnalysisSetFamily a) where
--   applySetRelation (SetFamily sr) args = applySetRelation sr args

--   applySetRelation (SetUnion x y) args = do
--     z3M mkOr [applySetRelation x args, applySetRelation y args]

--   applySetRelation (SetUnionSingle x (v, s)) args@[v',s'] = do
--     z3_v <- toZ3 v
--     z3_s <- toZ3 s

--     z3M mkOr [ applySetRelation x args
--              , z3M mkAnd [mkEq z3_v v', mkEq z3_s s']
--              ]

--   applySetRelation (SetIte (LatticeEqual sensX sensY) t f) args = do
--     z3_sensX <- toZ3 sensX
--     z3_sensY <- toZ3 sensY

--     eql <- mkEq z3_sensX z3_sensY

--     mkIte eql <$> applySetRelation t args <!> applySetRelation f args

--   applySetRelation (SetIte (In (v, s) x) t f) args = do
--     z3_v <- toZ3 v
--     z3_s <- toZ3 s

--     cond <- applySetRelation x [z3_v, z3_s]

--     mkIte cond <$> applySetRelation t args <!> applySetRelation f args

--   applySetRelation SetEmpty _args = error "applySetRelation: SE_Empty"


class ToZ3 a where
  toZ3 :: a -> Z3Converter AST


instance ToZ3 NodeId where
  toZ3 n = mkApp <$> lookupZ3FuncDecl n <!> pure []

instance ToZ3 Var where
  toZ3 (Var n) = mkApp <$> lookupZ3FuncDecl n <!> pure []

instance ToZ3 Sensitivity where
  toZ3 = toZ3 . (SensAtom :: Sensitivity -> SensExpr)

instance ToZ3 SensExpr where
  toZ3 s@(SensAtom _) =
    mkApp <$> (lookupZ3FuncDecl s) <!> pure []

  toZ3 s@(SensFamily (SensT x)) = do
    z3_t <- lookupZ3FuncDecl s
    mkAppM z3_t []

-- type Z3Cs a = (FreeVars a, Z3Equality (Z3Var a) a)

class (FreeVars a, Z3Equality (Z3Var a) a) => Z3Cs a
instance (FreeVars a, Z3Equality (Z3Var a) a) => Z3Cs a

type instance ReprC AnalysisSetFamily a = FreeVars a
type instance ReprC Z3Var a = FreeVars a

instance ToZ3 (SetConstraint Z3Cs AnalysisSetFamily) where
  toZ3 (lhs `SetConstr` rhs) =
    forallQuantifyFreeVars lhs $ \vars ->
      mkEq <$> toZ3 (vars, lhs) <!> toZ3 (vars, rhs)

-- data BoolExpr f where
--   In :: a -> SetExpr f a -> BoolExpr f
--   (:&&:) :: BoolExpr f -> BoolExpr f -> BoolExpr f
--   LatticeEqual :: LatticeExpr f a -> LatticeExpr f a -> BoolExpr f

-- data SetExpr f a where
--   SetFamily :: f a -> SetExpr f a
--   SetUnion :: SetExpr f a -> SetExpr f a -> SetExpr f a
--   SetUnionSingle :: SetExpr f a -> a -> SetExpr f a
--   SetCompr :: Lam (a -> SetExpr f b) -> Lam (a -> BoolExpr f) -> SetExpr f a -> SetExpr f a
--   SetIte :: BoolExpr f -> SetExpr f a -> SetExpr f a -> SetExpr f a
--   SetEmpty :: SetExpr f a

-- forallQuantifyFreeVars :: forall f a. (FreeVars a) => f a -> (Z3Var a -> Z3Converter AST) -> Z3Converter AST

instance (FreeVars a, Z3Equality (Z3Var a) a) => ToZ3 (Z3Var a, SetExpr AnalysisSetFamily a) where
  toZ3 (z3Var, se) =
    case se of
      SetFamily sf -> toZ3 (z3Var, sf)
      SetUnion a b -> z3M mkOr [toZ3 (z3Var, a), toZ3 (z3Var, b)]
      SetUnionSingle e x -> z3M mkOr [toZ3 (z3Var, e), z3Eq z3Var x]
      SetCompr lam@(Lam f) (Lam p) x -> do
        v <- lamRepr lam
        forallQuantifyZ3Var v $ do
          body <- toZ3 (f (LamVar v))
          cond <- toZ3 (p (LamVar v))

          inX <- toZ3 (LiftedVar (LamVar v) `In` x)

          mkImplies <$> (mkAnd [cond, inX]) <!> pure body
      SetEmpty -> mkFalse
      SetIte b t f ->
        mkIte <$> toZ3 b <*> toZ3 t <!> toZ3 f


-- data BoolExpr f where
--   In :: Lifted a -> SetExpr f a -> BoolExpr f
--   (:&&:) :: BoolExpr f -> BoolExpr f -> BoolExpr f
--   LatticeEqual :: LatticeExpr f a -> LatticeExpr f a -> BoolExpr f

-- instance toZ3 (Lifted Sensitivity) 

instance ToZ3 (BoolExpr AnalysisSetFamily) where
  toZ3 (LiftedValue x `In` xs) = do
    x' <- toZ3 x
    undefined

instance FreeVars a => ToZ3 (SetExpr AnalysisSetFamily a) where

instance FreeVars a => ToZ3 (Z3Var a, AnalysisSetFamily a) where
  toZ3 (z3Var, sf) = applySetRelation sf z3Var

-- instance ToZ3 (SetConstraint AnalysisSetFamily) where
--   toZ3 (lhs `SetConstr` SetEmpty) = do
--     forallQuantifyFreeVars lhs $ \vars -> do
--       mkEq <$> applySetRelation lhs vars <!> mkFalse

--   -- toZ3 (lhs@(Atom_E' _) `SetConstr` SE_Atom (SingleVar v0)) = do
--   --   (varSort, v_sym, v_var) <- mkSymVar "v" Var_Sort
--   --   z3_v0 <- toZ3 v0

--   --   mkForallConst [] [v_sym]
--   --     =<< mkIte <$> mkEq z3_v0 v_var
--   --               <*> (mkEq <$> applySetRelation lhs [v_var] <!> mkTrue)
--   --               <!> (mkEq <$> applySetRelation lhs [v_var] <!> mkFalse)

--   -- toZ3 (lhs@(Atom_E' _) `SetConstr` SE_Atom (SetFamily x)) =
--   --   forallQuantifyFreeVars lhs $ \vars ->
--   --     (mkEq <$> applySetRelation lhs vars <!> applySetRelation x vars)

--   -- toZ3 (lhs@(Atom_E' _) `SetConstr` SE_UnionSingle {}) = error "Assignment of E to a singleton of a variable/sensitivity pair"

--   -- toZ3 (lhs@(Atom_E' _) `SetConstr` SE_Union x y) =
--   --   forallQuantifyFreeVars lhs $ \vars -> do
--   --     the_or <- z3M mkOr [applySetRelation x vars, applySetRelation y vars]
--   --     mkEq <$> applySetRelation lhs vars <!> pure the_or



--   toZ3 (lhs `SetConstr` SetFamily x) =
--     forallQuantifyFreeVars lhs $ \vars ->
--       mkEq <$> applySetRelation lhs vars <!> applySetRelation x vars

--   -- toZ3 (_ `SetConstr` SE_Atom (SingleVar _)) = error "Assignment of a set family other than E to a singleton containing a variable (not a pair)"

--   toZ3 (lhs `SetConstr` SetUnion x y) =
--     forallQuantifyFreeVars lhs $ \vars -> do
--       the_or <- z3M mkOr [applySetRelation x vars, applySetRelation y vars]
--       mkEq <$> applySetRelation lhs vars <!> pure the_or

--   toZ3 (lhs `SetConstr` SetUnionSingle x v0 s0) = do

--     (varSort, v_sym, v_var) <- mkSymVar "v" Var_Sort
--     (sensSort, s_sym, s_var) <- mkSymVar "s" Sens_Sort
--     let vs = [v_var, s_var]

--     mkForallConst [] [v_sym, s_sym]
--       =<< (mkIte <$> z3M mkAnd [mkEq v_var =<< toZ3 v0, mkEq s_var =<< toZ3 s0]
--                  <*> (mkEq <$> applySetRelation lhs vs <!> mkTrue)
--                  <!> (mkEq <$> applySetRelation lhs vs <!> applySetRelation x vs))

--   toZ3 (lhs `SetConstr` SetIte (LatticeEqual sensX sensY) t f) = do
--     (varSort, v_sym, v_var) <- mkSymVar "v" Var_Sort
--     (sensSort, s_sym, s_var) <- mkSymVar "s" Sens_Sort
--     let vs = [v_var, s_var]

--     z3_sensX <- toZ3 sensX
--     z3_sensY <- toZ3 sensY

--     eql <- mkEq z3_sensX z3_sensY

--     z3_t <- applySetRelation t vs
--     z3_f <- applySetRelation f vs

--     mkForallConst [] [v_sym, s_sym]
--       =<< (mkIte eql <$> (mkEq <$> applySetRelation lhs vs <!> pure z3_t)
--                      <!> (mkEq <$> applySetRelation lhs vs <!> pure z3_f))

--   toZ3 (lhs `SetConstr` SetIte (In (v, s) x) t f) = do

--     z3_v <- toZ3 v
--     z3_s <- toZ3 s

--     cond <- applySetRelation x [z3_v, z3_s]

--     (varSort, v_sym, v_var) <- mkSymVar "v" Var_Sort
--     (sensSort, s_sym, s_var) <- mkSymVar "s" Sens_Sort
--     let vs = [v_var, s_var]

--     z3_t <- applySetRelation t vs
--     z3_f <- applySetRelation f vs

--     mkForallConst [] [v_sym, s_sym]
--       =<< (mkIte cond <$> (mkEq <$> applySetRelation lhs vs <!> pure z3_t)
--                       <!> (mkEq <$> applySetRelation lhs vs <!> pure z3_f))

-- constraintsToZ3 :: Constraints -> Z3Converter ()
-- constraintsToZ3 cs = do
--   asts <- mapM toZ3 cs

--   let astsZipped = zip asts [0..]

--   forM_ astsZipped $ \(ast, n) -> do
--     track <- mkFreshBoolVar $ "ast" ++ show n

--     {- trackingAssert track -}
--     assert ast

-- nodeIdToLoc :: CTranslationUnit (NodeInfo, NodeId) -> NodeId -> (NodeId, Maybe Position)
-- nodeIdToLoc transUnit nodeId =
--   (nodeId, fmap posOf . lookup nodeId $ foldMap (\(info, nodeId') -> [(nodeId', info)]) transUnit)

-- nodeIdLocInfo :: [(NodeId, Maybe Position)] -> String
-- nodeIdLocInfo = unlines . map go
--   where
--     go (nodeId, pos_maybe) = ppr nodeId ++ ": " ++
--       case pos_maybe of
--         Nothing -> "<no position info>"
--         Just pos -> show pos

-- getAnns :: CTranslationUnit a -> [a]
-- getAnns = foldMap (:[])

-- data GCC_NoIncludes = GCC_NoIncludes FilePath

-- instance Preprocessor GCC_NoIncludes where
--   parseCPPArgs (GCC_NoIncludes path) = parseCPPArgs (newGCC path)

--   runCPP (GCC_NoIncludes path) cpp_args = do
--     let tempFile = replaceExtension (inputFile cpp_args) "i-sed"

--     (_, Just h1, _, p1) <- createProcess (proc "sed" ["s/^[[:space:]]*#[[:space:]]*include.*//", inputFile cpp_args]) { std_out = CreatePipe }
--     (_, _, _, p2)       <- createProcess (proc path (buildCppArgs' cpp_args ++ ["-E", "-"])) { std_in = UseHandle h1 }

--     waitForProcess p1
--     waitForProcess p2

-- -- Adapted from Language.C.System.GCC to avoid using the input file (so
-- -- that stdin is used instead)
-- buildCppArgs' :: CppArgs -> [String]
-- buildCppArgs' (CppArgs options extra_args _tmpdir _input_file output_file_opt) =
--        (concatMap tOption options)
--     ++ outputFileOpt
--     ++ extra_args
--     where
--     tOption (IncludeDir incl)  = ["-I",incl]
--     tOption (Define key value) = [ "-D" ++ key ++ (if null value then "" else "=" ++ value) ]
--     tOption (Undefine key)     = [ "-U" ++ key ]
--     tOption (IncludeFile f)    = [ "-include", f]
--     outputFileOpt = concat [ ["-o",output_file] | output_file <- maybeToList output_file_opt ]

-- gccPath :: FilePath
-- gccPath = "/usr/bin/gcc"

-- main :: IO ()
-- main = do
--   let fileName = "../test.c"

--   let gcc = GCC_NoIncludes gccPath

--   stream_either <- runPreprocessor gcc $ CppArgs
--     { cppOptions = []
--     , extraOptions = ["-nostdinc"]
--     , cppTmpDir = Nothing
--     , inputFile = fileName
--     , outputFile = Nothing
--     }

--   case stream_either of
--     Left err -> putStrLn $ "Preprocessing failed: " ++ show err
--     Right stream -> do
--       case parseC stream (initPos fileName) of
--         Left err -> error (show err)
--         Right parsed -> do
--           let parsed' = flip runState (NodeId 0) $ traverse (\x -> (x,) <$> newNodeId) parsed
--               parsed'' = first (fmap snd) parsed'
--               constraints = execConstraintGen $ transformM (constAction handleTransUnit) parsed''
--               nodeLocs = map (nodeIdToLoc (fst parsed')) (getAnns (fst parsed''))
--               theNodeIds = getNodeIds constraints

--           -- putStrLn $ ppr constraints
--           -- hPutStrLn stderr $ ppr constraints

--           let tPairs = getTNodes constraints
--               sPairs = getSPairs constraints

--           (r, modelStr_maybe) <- evalZ3Converter (Set.toList (getVars constraints))
--                                                  (Set.toList theNodeIds)
--                                                  (Set.toList sPairs)
--                                                  (Set.toList tPairs)
--                                                  (constraintsToZ3 constraints)
--           -- print r


--           putStrLn $ genDOT' constraints
--           hPrint stderr r

--           -- case modelStr_maybe of
--           --   Left core -> putStrLn $ "Unsat core:\n" <> unlines core
--           --   Right modelStr -> do
--           --     putStrLn $ "Model:\n" <> modelStr

