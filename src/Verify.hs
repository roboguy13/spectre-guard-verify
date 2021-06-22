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
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE InstanceSigs #-}

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

data Z3Sort = Sens_Sort | Var_Sort | VarSens_Sort | Node_Sort deriving (Show, Eq)

data Z3Info =
  Z3Info
  { z3Info_setFamilyDecls :: forall a. AnalysisSetFamily a -> FuncDecl
  , z3Info_sensExprDecls :: SensExpr -> FuncDecl
  , z3Info_varDecls :: Var -> FuncDecl
  , z3Info_nodeDecls :: NodeId -> FuncDecl
  , z3Info_sorts :: Z3Sort -> Sort
  , z3Info_varSensConstructor :: FuncDecl
  , z3Info_varSens_varProj :: FuncDecl
  , z3Info_varSens_sensProj :: FuncDecl
  , z3Info_sens_setJoin :: FuncDecl
  }

newtype Z3Converter a = Z3Converter { getZ3Converter :: ReaderT Z3Info (StateT Int Z3) a }
  deriving (Functor, Applicative, Monad, MonadReader Z3Info, MonadState Int, MonadZ3, MonadIO)

defineZ3Names :: [Var] -> [NodeId] -> Z3 Z3Info
defineZ3Names vars nodeIds = do
    let makeSyms str = mapM (\x -> mkStringSymbol (str ++ show x))
        nodeIdNums = map getNodeId nodeIds

    c_exit_sym <- mkStringSymbol "C_exit"
    c_entry_sym <- mkStringSymbol "C_entry"
    s_sym <- mkStringSymbol "S"
    t_sym <- mkStringSymbol "T"

    -- e_syms <- makeSyms "E" nodeIdNums
    e_sym <- mkStringSymbol "E"

    b_sym <- mkStringSymbol "B"

    node_syms <- makeSyms "n" nodeIdNums
    var_syms <- makeSyms "v" (map (\(Var v) -> v) vars)
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

    varSens_type_sym <- mkStringSymbol "VarSens"

    varSens_var_sym <- mkStringSymbol "VS_Var"
    varSens_sens_sym <- mkStringSymbol "VS_Sens"

    (varSens_sort, varSens_constructor, [varSens_var, varSens_sens]) <- mkTupleSort varSens_type_sym [(varSens_var_sym, var_sort), (varSens_sens_sym, sens_sort)]

    varSens_set_sort <- mkSetSort varSens_sort

    node_fns <- zip nodeIds <$> getDatatypeSortConstructors node_sort
    var_fns <- zip vars <$> getDatatypeSortConstructors var_sort
    [public_fn, secret_fn] <- getDatatypeSortConstructors sens_sort


    sens_join_sym <- mkStringSymbol "sens_join"
    sens_join <- mkFuncDecl sens_join_sym [sens_sort, sens_sort] sens_sort

    public <- mkApp public_fn []
    secret <- mkApp secret_fn []

    assert =<< (mkEq <$> (mkApp sens_join [public, public]) <!> pure public)
    assert =<< (mkEq <$> (mkApp sens_join [secret, public]) <!> pure secret)
    assert =<< (mkEq <$> (mkApp sens_join [public, secret]) <!> pure secret)
    assert =<< (mkEq <$> (mkApp sens_join [secret, secret]) <!> pure secret)

    sens_set_sort <- mkSetSort sens_sort

    sens_setJoin_sym <- mkStringSymbol "sens_setJoin"
    sens_setJoin <- mkFuncDecl sens_setJoin_sym [sens_set_sort] sens_sort

    do
      xs <- mkFreshVar "xs" sens_set_sort
      xs_sym <- toApp xs
      assert =<<
        mkForallConst [] [xs_sym]
          =<< (mkIte <$> (mkSetMember secret xs)
                     <*> (mkEq <$> (mkApp sens_setJoin [xs]) <!> pure secret)
                     <!> (mkEq <$> (mkApp sens_setJoin [xs]) <!> pure public))
      assert =<< (mkEq <$> (z3M (mkApp sens_setJoin) [mkEmptySet sens_sort]) <!> pure public)


    bool_sort <- mkBoolSort

    let buildFn sorts resultSort = mapM (\n -> mkFuncDecl n sorts resultSort)

    c_exit_fn <- mkFuncDecl c_exit_sym [node_sort] varSens_set_sort
    c_entry_fn <- mkFuncDecl c_entry_sym [node_sort] varSens_set_sort
    s_fn <- mkFuncDecl s_sym [node_sort, node_sort] varSens_set_sort

    sens_set_sort <- mkSetSort sens_sort
    var_set_sort <- mkSetSort var_sort

    t_fn <- mkFuncDecl t_sym [node_sort] sens_sort

    b_fn <- mkFuncDecl b_sym [node_sort] var_set_sort

    e_fn <- mkFuncDecl e_sym [node_sort] var_set_sort

    -- e_fns <- zip nodeIds <$> buildFn [var_sort] bool_sort e_syms

    let lookup' x xs =
          case lookup x xs of
            Nothing -> error $ "defineZ3Names: Internal Z3 lookup failed: " ++ show x
            Just z -> z

    return $ Z3Info
       { z3Info_setFamilyDecls = \case
            C_Exit _n -> c_exit_fn
            C_Entry _n -> c_entry_fn
            S_Family _x _y -> s_fn
            B_Family _n -> b_fn
            E_Family _n -> e_fn

       , z3Info_sensExprDecls = \case
            SensAtom Public -> public_fn
            SensAtom Secret -> secret_fn
            SensT _x -> t_fn

       , z3Info_varDecls = \v -> lookup' v var_fns
       , z3Info_nodeDecls = \n -> lookup' n node_fns
       , z3Info_sorts = \case
          Sens_Sort -> sens_sort
          Var_Sort -> var_sort
          VarSens_Sort -> varSens_sort
          Node_Sort -> node_sort

       , z3Info_varSensConstructor = varSens_constructor
       , z3Info_varSens_varProj = varSens_var
       , z3Info_varSens_sensProj = varSens_sens
       , z3Info_sens_setJoin = sens_setJoin
       }

tDef :: NodeId -> ConstraintE Z3Repr
tDef n =
  toZ3Repr (SensT n) :=: rhs
  where
    rhs :: Z3Repr SensExpr
    rhs =
      lub (setCompr
              varSens_sensProj

              (\vs -> varSens_varProj vs
                       `in_`
                      value (E_Family n))

              (toZ3Repr (C_Entry n)))

bDef :: NodeId -> ConstraintE Z3Repr
bDef n =
  toZ3Repr (B_Family n) :=: rhs
  where
    rhs :: Z3Repr (AnalysisSetFamily Var)
    rhs =
      setCompr
        (\vs -> varSens_varProj vs)
        (\_ -> true)
        (toZ3Repr (C_Exit n))

sDef :: NodeId -> NodeId -> ConstraintE Z3Repr
sDef m n =
  toZ3Repr (S_Family m n) :=: rhs
  where
    rhs :: Z3Repr (AnalysisSetFamily (Var, SensExpr))
    rhs =
      setCompr
        (\vs ->
            let (v, s) = (varSens_varProj vs
                         ,varSens_sensProj vs)
            in
            varSens_pair v
                         (ite (v `in_` toZ3Repr (B_Family m))
                              (toZ3Repr (SensAtom Secret))
                              s))
        (\_ -> true)
        (toZ3Repr (C_Exit n))

consistentSensitivity :: NodeId -> Z3Converter AST
consistentSensitivity n = do
  (var_sort, v_sym, v) <- mkSymVar "v" Var_Sort
  (sens_sort, s_sym, s) <- mkSymVar "s" Sens_Sort
  (_, s2_sym, s2) <- mkSymVar "s2" Sens_Sort

  c_exit <- toZ3 (C_Exit n)

  varSens <- z3Info_varSensConstructor <$> ask

  mkForallConst [] [v_sym, s_sym, s2_sym]
    =<< (mkImplies <$> (z3M mkAnd [mkSetMember <$> mkApp varSens [v, s] <!> pure c_exit, mkSetMember <$> mkApp varSens [v, s2] <!> pure c_exit])
                   <!> (mkEq s s2))

correctnessCondition :: [NodeId] -> Z3Converter ()
correctnessCondition nodeIds = do
  asts <- mapM consistentSensitivity nodeIds
  mapM_ trackingAssert asts

evalZ3Converter :: [Var] -> [NodeId] -> [(NodeId, NodeId)] -> [NodeId] -> Z3Converter a -> IO (Result, Either [String] String)
evalZ3Converter vars nodeIds sPairs tNodes (Z3Converter conv) = evalZ3 $ do
  params <- mkParams
  paramsSetBool params <$> mkStringSymbol "core.minimize" <!> pure True
  solverSetParams params

  z3Info <- defineZ3Names vars nodeIds

  -- case (generateS's sPairs, generateT's tNodes, correctnessCondition nodeIds) of
  --   (Z3Converter generateS's_Z3, Z3Converter generateT's_Z3, Z3Converter correctnessCondition) -> do
  --     str <- flip evalStateT 0 $ runReaderT (generateS's_Z3 >> generateT's_Z3 >> conv >> correctnessCondition >> solverToString) z3Info
  --     -- liftIO $ hPutStrLn stderr str

  flip evalStateT 0 $ flip runReaderT z3Info $ getZ3Converter $ do
    mapM_ (toZ3 . uncurry sDef) sPairs
    mapM_ (toZ3 . tDef) tNodes
    mapM_ (toZ3 . bDef) (map snd sPairs)
    Z3Converter conv
    correctnessCondition nodeIds

  str <- solverToString
  liftIO $ hPutStrLn stderr str
  liftIO $ hFlush stderr

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

instance Z3FuncDecl Var where
  lookupZ3FuncDecl = lookupZ3' z3Info_varDecls

instance Z3FuncDecl NodeId where
  lookupZ3FuncDecl = lookupZ3' z3Info_nodeDecls

lookupZ3' :: (Z3Info -> (a -> r)) -> a -> Z3Converter r
lookupZ3' accessor x = do
  f <- fmap accessor ask
  return $ f x

lookupZ3Sort :: Z3Sort -> Z3Converter Sort
lookupZ3Sort = lookupZ3' z3Info_sorts


  -- , z3Info_varSensConstructor :: FuncDecl

varSens_pair :: Z3Repr Var -> Z3Repr SensExpr -> Z3Repr (Var, SensExpr)
varSens_pair xM yM = Z3Repr $ do
  x <- getZ3Repr xM
  y <- getZ3Repr yM
  construct <- z3Info_varSensConstructor <$> ask
  mkApp construct [x, y]

varSens_varProj :: Z3Repr (Var, SensExpr) -> Z3Repr Var
varSens_varProj varSensM = Z3Repr $ do
  varSens <- getZ3Repr varSensM
  proj <- z3Info_varSens_varProj <$> ask
  mkApp proj [varSens]

varSens_sensProj :: Z3Repr (Var, SensExpr) -> Z3Repr SensExpr
varSens_sensProj varSensM = Z3Repr $ do
  varSens <- getZ3Repr varSensM
  proj <- z3Info_varSens_sensProj <$> ask
  mkApp proj [varSens]

mkAppM :: MonadZ3 z3 => FuncDecl -> [z3 AST] -> z3 AST
mkAppM decl = z3M (mkApp decl)

z3M :: MonadZ3 z3 => ([a] -> z3 b) -> [z3 a] -> z3 b
z3M f argsM =
  f =<< sequence argsM

lookupSetFamilyFn :: AnalysisSetFamily a -> Z3Converter (FuncDecl, [AST])
lookupSetFamilyFn sf@(C_Exit n) = do
  f <- lookupZ3FuncDecl sf
  (f,) <$> sequence [toZ3 n]

lookupSetFamilyFn sf@(C_Entry n) = do
  f <- lookupZ3FuncDecl sf
  (f,) <$> sequence [toZ3 n]

lookupSetFamilyFn sf@(S_Family x y) = do
  f <- lookupZ3FuncDecl sf
  (f,) <$> sequence [toZ3 x, toZ3 y]

lookupSetFamilyFn sf@(B_Family n) = do
  f <- lookupZ3FuncDecl sf
  (f,) <$> sequence [toZ3 n]

lookupSetFamilyFn sf@(E_Family n) = do
  f <- lookupZ3FuncDecl sf
  (f,) <$> sequence [toZ3 n]

applyFamilyFn :: AnalysisSetFamily a -> [AST] -> Z3Converter AST
applyFamilyFn sf0 restArgs = do
  (sf, args) <- lookupSetFamilyFn sf0
  mkApp sf (args ++ restArgs)


class BaseVar a where
  baseVarPrefix_Sort :: proxy a -> (String, Z3Sort)

instance BaseVar (SensExpr) where
  baseVarPrefix_Sort _ = ("s", Sens_Sort)

instance BaseVar Var where
  baseVarPrefix_Sort _ = ("v", Var_Sort)

class FreeVars a where
  freeVars :: f a -> Z3Converter [(Sort, App, AST)]
  mkZ3Var :: Z3Converter (Z3Var a)

-- lamRepr :: FreeVars a => Lam Z3Cs (a -> b) -> Z3Converter (Z3Var a)
-- lamRepr _ = mkZ3Var

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

instance FreeVars (SensExpr) where
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

class ToZ3 a where
  toZ3 :: a -> Z3Converter AST

instance ToZ3 NodeId where
  toZ3 n = mkApp <$> lookupZ3FuncDecl n <!> pure []

instance ToZ3 Var where
  toZ3 n = mkApp <$> lookupZ3FuncDecl n <!> pure []

instance ToZ3 Sensitivity where
  toZ3 = toZ3 . (SensAtom :: Sensitivity -> SensExpr)

instance ToZ3 SensExpr where
  toZ3 x = mkApp <$> (lookupZ3FuncDecl x) <!> pure []

instance ToZ3 (AnalysisSetFamily a) where
  toZ3 = (`applyFamilyFn` [])

instance ToZ3 (ConstraintE Z3Repr) where
  toZ3 (x :=: y) = mkEq <$> getZ3Repr x <!> getZ3Repr y

newtype Z3Repr (a :: *) = Z3Repr { getZ3Repr :: Z3Converter AST }
  deriving (Functor)

toZ3Repr :: ToZ3 a => a -> Z3Repr a
toZ3Repr = Z3Repr . toZ3

z3ReprLift :: (AST -> Z3Converter AST) -> (Z3Repr a -> Z3Repr b)
z3ReprLift f xM = Z3Repr (f =<< getZ3Repr xM)

z3ReprLift2 :: (AST -> AST -> Z3Converter AST) -> (Z3Repr a -> Z3Repr b -> Z3Repr c)
z3ReprLift2 f xM yM = Z3Repr (f <$> getZ3Repr xM <!> getZ3Repr yM)

z3ReprLift2List :: ([AST] -> Z3Converter AST) -> (Z3Repr a -> Z3Repr b -> Z3Repr c)
z3ReprLift2List f xM yM = Z3Repr $ do
  x <- getZ3Repr xM
  y <- getZ3Repr yM
  f [x, y]

instance BoolExpr Z3Repr where
  type EqualCt Z3Repr = ((~) SensExpr)

  in_ = z3ReprLift2 mkSetMember

  (^&&^) = z3ReprLift2List mkAnd

  equal = z3ReprLift2 mkEq

  true = Z3Repr mkTrue
  false = Z3Repr mkFalse

  ite condM tM fM = Z3Repr $ do
    cond <- getZ3Repr condM
    t <- getZ3Repr tM
    f <- getZ3Repr fM
    mkIte cond t f

class Z3Set set where
  getZ3SetSort :: Proxy set -> Z3Converter Sort
  toZ3Set :: set a -> Z3Converter AST

instance Z3Set AnalysisSetFamily where
  getZ3SetSort Proxy = lookupZ3Sort VarSens_Sort
  toZ3Set = toZ3

class GetSort a where
  getElemSort :: SetCt Z3Repr set => Z3Repr (set a) -> Z3Sort

instance GetSort Var where
  getElemSort _ = Var_Sort

instance GetSort SensExpr where
  getElemSort _ = Sens_Sort

instance GetSort (Var, SensExpr) where
  getElemSort _ = VarSens_Sort

instance ToZ3 (Var, SensExpr) where
  toZ3 (v, s) = do
    construct <- z3Info_varSensConstructor <$> ask
    z3M (mkApp construct) [toZ3 v, toZ3 s]

instance Value Z3Repr where
  type ValueCt Z3Repr = ToZ3
  value = toZ3Repr

instance SetExpr Z3Repr where
  type SetCt Z3Repr = Z3Set
  type SetElemCt Z3Repr = GetSort

  setValue = Z3Repr . toZ3Set

  union = z3ReprLift2List mkSetUnion
  unionSingle = z3ReprLift2 (flip mkSetAdd)

  empty :: forall (set :: * -> *) a. SetCt Z3Repr set => Z3Repr (set a)
  empty = Z3Repr $ do
    sort <- getZ3SetSort (Proxy @set)
    mkEmptySet sort

  setCompr f p sM = Z3Repr $ do
    s <- getZ3Repr sM

    (_, x_sym, x) <- mkSymVar "x" (getElemSort sM)

    pX <- getZ3Repr (p (Z3Repr (pure x)))
    fX <- getZ3Repr (f (Z3Repr (pure x)))

    set_sort <- mkSetSort =<< getSort fX

    uniq <- get
    modify succ

    compr_sym <- mkStringSymbol ("compr" <> show uniq)

    compr <- mkConst compr_sym set_sort

    assert =<< (mkForallConst [] [x_sym]
      =<<
        (mkIff <$> (z3M mkAnd [mkSetMember x s, pure pX])
               <!> (mkSetMember fX compr)))

    return compr

instance LatticeExpr Z3Repr where
  type LatticeCt Z3Repr = ((~) SensExpr)

  lub setM = Z3Repr $ do
    set <- getZ3Repr setM
    setJoin <- z3Info_sens_setJoin <$> ask

    mkApp setJoin [set]

constraintsToZ3 :: Constraints Z3Repr -> Z3Converter ()
constraintsToZ3 cs = mapM_ toZ3 cs


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

data GCC_NoIncludes = GCC_NoIncludes FilePath

instance Preprocessor GCC_NoIncludes where
  parseCPPArgs (GCC_NoIncludes path) = parseCPPArgs (newGCC path)

  runCPP (GCC_NoIncludes path) cpp_args = do
    let tempFile = replaceExtension (inputFile cpp_args) "i-sed"

    (_, Just h1, _, p1) <- createProcess (proc "sed" ["s/^[[:space:]]*#[[:space:]]*include.*//", inputFile cpp_args]) { std_out = CreatePipe }
    (_, _, _, p2)       <- createProcess (proc path (buildCppArgs' cpp_args ++ ["-E", "-"])) { std_in = UseHandle h1 }

    waitForProcess p1
    waitForProcess p2

-- Adapted from Language.C.System.GCC to avoid using the input file (so
-- that stdin is used instead)
buildCppArgs' :: CppArgs -> [String]
buildCppArgs' (CppArgs options extra_args _tmpdir _input_file output_file_opt) =
       (concatMap tOption options)
    ++ outputFileOpt
    ++ extra_args
    where
    tOption (IncludeDir incl)  = ["-I",incl]
    tOption (Define key value) = [ "-D" ++ key ++ (if null value then "" else "=" ++ value) ]
    tOption (Undefine key)     = [ "-U" ++ key ]
    tOption (IncludeFile f)    = [ "-include", f]
    outputFileOpt = concat [ ["-o",output_file] | output_file <- maybeToList output_file_opt ]

gccPath :: FilePath
gccPath = "/usr/bin/gcc"

newNodeId :: State NodeId NodeId
newNodeId = do
  NodeId x <- get

  put (NodeId (succ x))

  return $ NodeId x

main :: IO ()
main = do
  let fileName = "../test.c"

  let gcc = GCC_NoIncludes gccPath

  stream_either <- runPreprocessor gcc $ CppArgs
    { cppOptions = []
    , extraOptions = ["-nostdinc"]
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
              results = execConstraintGen (void (transformM (constAction handleTransUnit) parsed'')) :: ConstraintGenResults Z3Repr

              constraints = cgConstraints results
              used = cgUsed results
              nodeLocs = map (nodeIdToLoc (fst parsed')) (getAnns (fst parsed''))
              theNodeIds = nodeIdsUsed used

          -- putStrLn $ ppr constraints
          -- hPutStrLn stderr $ ppr constraints

          let tPairs = tNodesUsed used
              sPairs = sPairsUsed used

          putStrLn $ "tNodes = " <> show tPairs
          putStrLn $ "sPairs = " <> show sPairs
          putStrLn $ "nodeIds = " <> show theNodeIds
          putStrLn $ "vars = " <> show (varsUsed used)
          -- putStrLn $ "nodeLocs = " <> show nodeLocs

          (r, modelStr_maybe) <- evalZ3Converter (Set.toList (varsUsed used))
                                                 (Set.toList theNodeIds)
                                                 (Set.toList sPairs)
                                                 (Set.toList tPairs)
                                                 (constraintsToZ3 constraints)
          -- print r


          -- putStrLn $ genDOT' constraints
          hPrint stderr r

          -- case modelStr_maybe of
          --   Left core -> putStrLn $ "Unsat core:\n" <> unlines core
          --   Right modelStr -> do
          --     putStrLn $ "Model:\n" <> modelStr

