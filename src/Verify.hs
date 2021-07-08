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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE PatternSynonyms #-}

{-# LANGUAGE QuantifiedConstraints #-}

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

import           Control.Exception hiding (assert)

import           Data.Generics.Uniplate.Data
import           Data.Bifunctor

import           Data.Typeable
import           Data.Proxy
import           Data.Kind
import           Data.Constraint

import           Data.Foldable

import qualified Data.ByteString as BS

import           Data.Maybe (maybeToList)

import qualified Data.List as L
import qualified Data.Set as Set

import           Orphans ()
import           Ppr
import           SetExpr
import           Pattern
import           ConstraintGen
import           DOT

generateDOT :: Bool
generateDOT = True

-- data Z3Var a = Z3Var { getZ3Var :: AST }

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

data Z3Sort = Sens_Sort | Var_Sort | VarSens_Sort | VarSensSet_Sort | SensSet_Sort | VarSet_Sort | Node_Sort deriving (Show, Eq)

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
  , z3Info_sens_join :: FuncDecl
  , z3Info_sens_le :: FuncDecl
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

    bool_sort <- mkBoolSort

    sens_le_sym <- mkStringSymbol "sens_le"
    sens_le <- mkFuncDecl sens_le_sym [sens_sort, sens_sort] bool_sort
    assert =<< mkApp sens_le [public, public]
    assert =<< mkApp sens_le [secret, secret]
    assert =<< mkApp sens_le [secret, public]
    assert =<< mkNot =<< mkApp sens_le [public, secret]

    sens_set_sort <- mkSetSort sens_sort

    sens_setJoin_sym <- mkStringSymbol "sens_setJoin"
    sens_setJoin <- mkFuncDecl sens_setJoin_sym [sens_set_sort] sens_sort

    -- do
    --   xs <- mkFreshVar "xs" sens_set_sort
    --   xs_sym <- toApp xs
    --   trackingAssert =<<
    --     mkForallConst [] [xs_sym]
    --       =<< (mkIte <$> (mkSetMember secret xs)
    --                  <*> (mkEq <$> (mkApp sens_setJoin [xs]) <!> pure secret)
    --                  <!> (mkEq <$> (mkApp sens_setJoin [xs]) <!> pure public))
    --   trackingAssert =<< (mkEq <$> (z3M (mkApp sens_setJoin) [mkEmptySet sens_sort]) <!> pure public)



    let buildFn sorts resultSort = mapM (\n -> mkFuncDecl n sorts resultSort)

    c_exit_fn <- mkFuncDecl c_exit_sym [node_sort] varSens_set_sort
    c_entry_fn <- mkFuncDecl c_entry_sym [node_sort] varSens_set_sort
    s_fn <- mkFuncDecl s_sym [node_sort, node_sort] varSens_set_sort

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
          VarSensSet_Sort -> varSens_set_sort
          VarSet_Sort -> var_set_sort
          SensSet_Sort -> sens_set_sort
          Node_Sort -> node_sort

       , z3Info_varSensConstructor = varSens_constructor
       , z3Info_varSens_varProj = varSens_var
       , z3Info_varSens_sensProj = varSens_sens
       , z3Info_sens_setJoin = sens_setJoin
       , z3Info_sens_join = sens_join
       , z3Info_sens_le = sens_le
       }

-- tDef :: NodeId -> AnalysisConstraint Z3Var
-- tDef n =
--   MonoidVal (SensT n) :=: rhs
--   where
--     rhs :: AnalysisExpr Z3Var SensExpr
--     rhs =
--       Lub (SetCompr
--               Snd
--               -- varSens_sensProj

--               (\vs -> Fst vs
--                        `In`
--                       value (E_Family n))

--               (SetFamily (C_Entry n)))

bDef :: NodeId -> AnalysisConstraint Z3Var
bDef n =
  SetFamily (B_Family n) :=: rhs
  where
    rhs :: AnalysisExpr Z3Var (SetE Var)
    rhs =
      SetCompr
        (\vs -> Fst vs)
        (\_ -> BoolVal True)
        (SetFamily (C_Exit n))

sDef :: NodeId -> NodeId -> AnalysisConstraint Z3Var
sDef m n =
  SetFamily (S_Family m n) :=: rhs
  where
    rhs :: AnalysisExpr Z3Var (SetE (Var, SensExpr))
    rhs =
      SetCompr
        (\vs ->
            let (v, s) = (Fst vs
                         ,Snd vs)
            in
            Pair v
                 (Ite (v `In` SetFamily (B_Family m))
                      (value (SensAtom Secret))
                      s))
        (\_ -> BoolVal True)
        (SetFamily (C_Exit n))

consistentSensitivity :: NodeId -> Z3Converter AST
consistentSensitivity n = do
  (var_sort, v_sym, v) <- mkSymVar "v" Var_Sort
  (sens_sort, s_sym, s) <- mkSymVar "s" Sens_Sort
  (_, s2_sym, s2) <- mkSymVar "s2" Sens_Sort

  -- c_exit_fn <- lookupZ3FuncDecl (C_Exit (error "consistentSensitivity: this should not be reached"))
  -- c_exit <- mkApp c_exit_fn [n]

  c_exit <- toZ3 (C_Exit n)

  varSens <- z3Info_varSensConstructor <$> ask

  public <- toZ3 Public
  secret <- toZ3 Secret

  mkForallConst [] [v_sym] =<<
    z3M mkAnd
      [ mkImplies <$> (mkSetMember <$> mkApp varSens [v, public] <!> pure c_exit)
                  <!> (mkNot =<< (mkSetMember <$> mkApp varSens [v, secret] <!> pure c_exit))

      , mkImplies <$> (mkSetMember <$> mkApp varSens [v, secret] <!> pure c_exit)
                  <!> (mkNot =<< (mkSetMember <$> mkApp varSens [v, public] <!> pure c_exit))
      ]

  -- -- mkForallConst [] [v_sym, s_sym, s2_sym]
  -- mkExistsConst [] [v_sym, s_sym, s2_sym]
  --   =<< (z3M mkAnd [mkSetMember <$> mkApp varSens [v, s] <!> pure c_exit, mkSetMember <$> mkApp varSens [v, s2] <!> pure c_exit, mkNot =<< mkEq s s2])
  --                  -- <!> (mkEq s s2))

-- TODO: Instead of keeping track of each entire model, could just keep
-- track of the variable sensitivity mismatch info
newtype AnalysisResult = MkAnalysisResult (Maybe [(NodeId, Maybe Model, String)])
  deriving Semigroup via Maybe [(NodeId, Maybe Model, String)]
  deriving Monoid via Maybe [(NodeId, Maybe Model, String)]

pattern Correct = MkAnalysisResult Nothing
pattern Incorrect x = MkAnalysisResult (Just x)

showResult :: AnalysisResult -> String
showResult Correct = "Correct"
showResult (Incorrect errs) =
  "Incorrect:"
    <> unlines (map go errs)
  where
    go (n, _, str) = "  - At node " <> show n <> ":\n" <> str <> "\n"

-- instance Show Model where
--   show = _ . showModel

-- instance Semigroup AnalysisResult where
--   Incorrect x <> Incorrect y = Incorrect x
--   _ <> Incorrect y = Incorrect y
--   Correct <> Correct = Correct

-- instance Monoid AnalysisResult where
--   mempty = Correct

correctnessCondition :: [NodeId] -> Z3Converter AnalysisResult
correctnessCondition nodeIds = fmap mconcat . forM nodeIds $ \n -> do
  -- fmap mconcat . forM nodeIds $ \n -> trackingAssert =<< mkNot =<< consistentSensitivity n

  -- assert =<< mkAnd =<< mapM consistentSensitivity nodeIds

  solverPush
  liftIO $ hPutStrLn stderr $ "checking node " ++ show n ++ "..."

  vsSort <- lookupZ3Sort VarSens_Sort

  -- ast <- mkFalse
  ast <- mkNot =<< consistentSensitivity n
  -- ast <- mkNot =<< (mkEq <$> toZ3 (C_Exit n) <!> mkEmptySet vsSort)

  assert ast
  astStr <- astToString ast

  liftIO $ hPutStrLn stderr $ unlines $ map ('\t':) $ lines astStr

  -- assert ast

  checkResult <- check
  result <- case checkResult of
               Sat -> do
                 liftIO $ hPutStrLn stderr "*** SAT ***"
                 (_, modelM) <- getModel
                 case modelM of
                   Nothing -> return $ Incorrect [(n, Nothing, "<no model>")]
                   Just model -> do
                     modelStr <- showModel model
                     -- error $ "Incorrect:\n" ++ modelStr
                     return $ Incorrect [(n, Just model, modelStr)]
               Unsat -> do
                 coreStr <- unlines <$> (mapM astToString =<< getUnsatCore)
                 liftIO $ hPutStrLn stderr $ "unsat core: " ++ coreStr
                 return Correct
               Undef -> do
                 -- solverPop 1

                 -- trackingAssert =<< consistentSensitivity n
                 checkResult' <- check

                 (_, modelM) <- getModel
                 modelStr <- case modelM of
                   Nothing -> return "<no model>"
                   Just model -> showModel model

                 -- error $ "<undef>: " ++ show n ++ "\n" ++ show checkResult'
                 error $ "<undef>: " ++ modelStr -- ++ show n ++ "\n" ++ show checkResult'

  liftIO $ hPutStrLn stderr "check done.\n\n"

  solverPop 1
  return result

makeT :: NodeId -> Z3Converter ()
makeT n = do
  -- sens's <- toZ3 (SetCompr Snd (\_ -> BoolVal True) (SetFamily (C_Entry n)) :: AnalysisExpr Z3Var (SetE SensExpr))
  -- contained <- toZ3 (MonoidVal (SensT n) `In` SetCompr Snd (\_ -> BoolVal True) (SetFamily (C_Entry n)) :: AnalysisExpr Z3Var Bool)

  tFn' <- lookupZ3FuncDecl (SensT n)
  tFn <- mkApp tFn' . (:[]) =<< toZ3 n

  c_entry <- toZ3 (SetFamily (C_Entry n) :: AnalysisExpr Z3Var (SetE (Var, SensExpr)))
  -- c_entry' <- lookupZ3FuncDecl (C_Entry n)

  (_, v_sym, v) <- mkSymVar "v" Var_Sort

  varSens <- z3Info_varSensConstructor <$> ask

  contained <-
    mkExistsConst [] [v_sym]
      =<< mkSelect c_entry =<< (mkApp varSens [v, tFn])

  sens_le <- z3Info_sens_le <$> ask
  sensProj <- z3Info_varSens_sensProj <$> ask

  -- (_, s_sym, s) <- mkSymVar "s" Sens_Sort
  (_, vs_sym, vs) <- mkSymVar "vs" VarSens_Sort
  least <-
    mkForallConst [] [vs_sym]
      =<< (mkImplies <$> (mkSetMember vs c_entry) <!> z3M (mkApp sens_le) [pure tFn, mkApp sensProj [vs]])

  assert =<< mkAnd [contained, least]

-- evalZ3Converter :: [Var] -> [NodeId] -> [(NodeId, NodeId)] -> [NodeId] -> Z3Converter () -> IO (Result, Either [String] String)
evalZ3Converter :: [Var] -> [NodeId] -> [(NodeId, NodeId)] -> [NodeId] -> Z3Converter () -> IO AnalysisResult
evalZ3Converter vars nodeIds sPairs tNodes conv = evalZ3 $ do
  params <- mkParams
  paramsSetBool params <$> mkStringSymbol "core.minimize" <!> pure True
  -- paramsSetSymbol params <$> mkStringSymbol "trace" <!> mkStringSymbol "true"
  solverSetParams params

  -- z3Info <- pure Z3Info {}
  z3Info <- defineZ3Names vars nodeIds

  -- case (generateS's sPairs, generateT's tNodes, correctnessCondition nodeIds) of
  --   (Z3Converter generateS's_Z3, Z3Converter generateT's_Z3, Z3Converter correctnessCondition) -> do
  --     str <- flip evalStateT 0 $ runReaderT (generateS's_Z3 >> generateT's_Z3 >> conv >> correctnessCondition >> solverToString) z3Info
  --     -- liftIO $ hPutStrLn stderr str

  flip evalStateT 0 $ flip runReaderT z3Info $ getZ3Converter $ do
    mapM_ (assert <=< toZ3 . uncurry sDef) sPairs
    -- mapM_ (trackingAssert <=< toZ3 . tDef) tNodes

    mapM makeT tNodes

    mapM_ (trackingAssert <=< toZ3 . bDef) (map snd sPairs)
    conv
    correctnessCondition nodeIds

  -- str <- solverToString
  -- liftIO $ hPutStrLn stderr str
  -- liftIO $ hFlush stderr

  -- _ <- check
  -- -- pure (r, Left [])

  -- (r, model) <- getModel
  -- modelOrCore <- case model of
  --   Nothing -> do
  --     core <- getUnsatCore
  --     Left <$> mapM astToString core
  --   Just m -> Right <$> showModel m
  -- pure (r, modelOrCore)

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

mkSymVar' :: (String, Z3Sort) -> Z3Converter (App, AST)
mkSymVar' p = do
  (_, y, z) <- uncurry mkSymVar p
  return (y, z)


class ToZ3 a where
  toZ3 :: a -> Z3Converter AST

instance ToZ3 NodeId where
  toZ3 n = mkApp <$> lookupZ3FuncDecl n <!> pure []

instance ToZ3 Var where
  toZ3 n = mkApp <$> lookupZ3FuncDecl n <!> pure []

instance ToZ3 Sensitivity where
  toZ3 = toZ3 . (SensAtom :: Sensitivity -> SensExpr)

instance ToZ3 SensExpr where
  toZ3 s@(SensT n) = do
    n' <- toZ3 n
    mkApp <$> (lookupZ3FuncDecl s) <!> pure [n']

  toZ3 x = mkApp <$> (lookupZ3FuncDecl x) <!> pure []

instance ToZ3 (AnalysisSetFamily a) where
  toZ3 = (`applyFamilyFn` [])

newtype Z3Var = Z3Var { getZ3Var :: AST }

instance ToZ3 Bool where
  toZ3 False = mkFalse
  toZ3 True  = mkTrue

instance ElemVal Z3Var where
  type ElemRepr Z3Var = GetElemSort

class GetElemSort a where
  getElemSort :: proxy a -> Z3Sort

instance GetElemSort a => GetElemSort (SetE a) where
  getElemSort _ = getElemSort (Proxy @a)

instance GetElemSort Var where
  getElemSort _ = Var_Sort

instance GetElemSort SensExpr where
  getElemSort _ = Sens_Sort

instance GetElemSort (Var, SensExpr) where
  getElemSort _ = VarSens_Sort

getSetSort :: GetElemSort a => proxy a -> Z3Sort
getSetSort p =
  case getElemSort p of
    Var_Sort -> VarSet_Sort
    Sens_Sort -> SensSet_Sort
    VarSens_Sort -> VarSensSet_Sort
    _ -> error "getSetSort: Invalid sort"

instance ToZ3 (Expr Z3Var Var SensExpr AnalysisSetFamily a) where
  toZ3 (SetFamily sf) = toZ3 sf
  toZ3 (MonoidVal v) = toZ3 v
  toZ3 (BaseVal v) = toZ3 v
  toZ3 (BoolVal b) = toZ3 b

  toZ3 (In x xs) = mkSetMember <$> toZ3 x <!> toZ3 xs
  toZ3 (And x y) = do
    x' <- toZ3 x
    y' <- toZ3 y
    mkAnd [x', y']

  toZ3 (Ite c t f) = do
    c' <- toZ3 c
    t' <- toZ3 t
    f' <- toZ3 f
    mkIte c' t' f'

  toZ3 (BaseEqual x y) = mkEq <$> toZ3 x <!> toZ3 y
  toZ3 (MonoidEqual x y) = mkEq <$> toZ3 x <!> toZ3 y

  toZ3 (VarRepr (Z3Var v)) = return v

  toZ3 (Pair x y) = do
    construct <- z3Info_varSensConstructor <$> ask
    z3M (mkApp construct) [toZ3 x, toZ3 y]

  toZ3 (Fst x) = do
    proj <- z3Info_varSens_varProj <$> ask
    z3M (mkApp proj) [toZ3 x]

  toZ3 (Snd x) = do
    proj <- z3Info_varSens_sensProj <$> ask
    z3M (mkApp proj) [toZ3 x]

  toZ3 (Union x y) = do
    x' <- toZ3 x
    y' <- toZ3 y
    mkSetUnion [x', y']

  toZ3 (UnionSingle xs x) = do
    xs' <- toZ3 xs
    x' <- toZ3 x
    xs_str <- astToString xs'
    x_str <- astToString x'

    -- liftIO $ putStrLn $ "(" ++ xs_str ++ ", " ++ x_str ++ ")"

    mkSetAdd xs' x'
  toZ3 Empty = mkEmptySet =<< lookupZ3Sort (getElemSort (Proxy @a))

  toZ3 (SetCompr f p xs) = do
    xs' <- toZ3 xs
    (_, x_sym, x) <- mkSymVar "x" (getElemSort xs)
    let xVar = VarRepr (Z3Var x)

    let pX = p xVar
        fX = f xVar

    pX' <- toZ3 pX
    fX' <- toZ3 fX

    set_sort <- lookupZ3Sort (getSetSort fX)

    uniq <- get
    modify succ

    compr_sym <- mkStringSymbol ("compr" <> show uniq)

    compr <- mkConst compr_sym set_sort

    trackingAssert =<< mkForallConst [] [x_sym]
      =<<
        (mkImplies <$> (z3M mkAnd [mkSetMember x xs', pure pX'])
               <!> (mkSetMember fX' compr))

    return compr

  toZ3 (Lub xs) = do
    xs' <- toZ3 xs
    setJoin <- z3Info_sens_setJoin <$> ask

    mkApp setJoin [xs']

instance ToZ3 (AnalysisConstraint Z3Var) where
  toZ3 (x :=: y) = do
    -- liftIO $ putStrLn "--- constraint ---"
    x' <- toZ3 x --getZ3Repr x

    x_str <- astToString x'
    -- liftIO $ putStrLn $ "- " <> x_str

    y' <- toZ3 y --getZ3Repr y
    y_str <- astToString y'
    -- liftIO $ putStrLn $ "- " <> y_str

    -- liftIO $ putStrLn "------------------"
    mkEq x' y'

  toZ3 (x :>: y) = do
    x' <- toZ3 x
    y' <- toZ3 y
    mkSetSubset y' x'

constraintsToZ3 :: Constraints Z3Var -> Z3Converter ()
constraintsToZ3 cs = do
  forM cs
    (\c -> do
      ast <- toZ3 c

      astString <- astToString ast
      -- unless generateDOT $
      liftIO $ hPutStrLn stderr $ "constraint: {\n" ++ astString  ++ "\n}"

      trackingAssert ast)
  return ()


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

-- showConstraint :: ConstraintE Z3Repr -> String
-- showConstraint (x :=: y) = undefined

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
              constraints = execConstraintGen (void (transformM (constAction handleTransUnit) parsed'')) -- :: ConstraintGenResults

              used = getUsedIds constraints
              nodeLocs = map (nodeIdToLoc (fst parsed')) (getAnns (fst parsed''))
              theNodeIds = nodeIdsUsed used

          -- putStrLn $ ppr constraints
          -- hPutStrLn stderr $ ppr constraints

          let tPairs = tNodesUsed used
              sPairs = sPairsUsed used

          hPrint stderr parsed''

          -- print parsed''

          -- putStrLn $ "tNodes = " <> show tPairs
          -- putStrLn $ "sPairs = " <> show sPairs
          -- putStrLn $ "nodeIds = " <> show theNodeIds
          -- putStrLn $ "vars = " <> show (varsUsed used)

          -- putStrLn $ "nodeLocs = " <> show nodeLocs

          when generateDOT $ putStrLn $ genDOT' constraints

          result  <- evalZ3Converter (Set.toList (varsUsed used))
                                                 (Set.toList theNodeIds)
                                                 (Set.toList sPairs)
                                                 (Set.toList tPairs)
                                                 (constraintsToZ3 constraints)

          return ()

          -- hPrint stderr result
          hPutStrLn stderr (showResult result)

          -- -- print r


          -- -- putStrLn $ genDOT' constraints
          -- hPrint stderr r
          -- -- hPrint stderr modelStr_maybe

          -- case modelStr_maybe of
          --   Left core -> putStrLn $ "Unsat core:\n" <> unlines core
          --   Right modelStr -> do
          --     putStrLn $ "Model:\n" <> modelStr

