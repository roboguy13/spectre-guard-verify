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

-- {-# OPTIONS_GHC -Wall -Wno-unused-imports #-}

import           Language.C
import           Language.C.Data.Ident

import           Z3.Monad

import           Control.Monad.State
import           Control.Monad.Reader

import           Data.Generics.Uniplate.Data
import           Data.Bifunctor

import           Data.Typeable

import           Orphans ()
import           Ppr
import           SetExpr
import           ConstraintGen

data Z3Name where
  Z3_C_Exit :: Z3Name
  Z3_C_Entry :: Z3Name
  Z3_S :: Z3Name
  Z3_E :: Z3Name
  Z3_T :: Z3Name
  Z3_Node :: NodeId -> Z3Name
  Z3_Var :: Int -> Z3Name
  Z3_Sens :: Sensitivity -> Z3Name

deriving instance Show Z3Name
deriving instance Eq Z3Name

-- class HEq f where
--   heq :: f a -> f b -> Maybe (a :~: b)

-- data DPair f g = forall t. DPair (f t) (g t)

-- instance HEq Z3Name where
--   heq Z3_C_Exit Z3_C_Exit = Just Refl
--   heq Z3_C_Entry Z3_C_Entry = Just Refl
--   heq Z3_S Z3_S = Just Refl
--   heq Z3_E Z3_E = Just Refl
--   heq Z3_T Z3_T = Just Refl
--   heq (Z3_Node x) (Z3_Node y)
--     | x == y = Just Refl
--   heq (Z3_Var x) (Z3_Var y)
--     | x == y = Just Refl
--   heq _ _ = Nothing

data Z3Sort = Sens_Sort | Var_Sort | Node_Sort deriving (Show, Eq)

data Z3Info =
  Z3Info
  { z3Info_assocs :: [(Z3Name, FuncDecl)]
  , z3Info_sorts :: [(Z3Sort, Sort)]
  }

newtype Z3Converter a = Z3Converter (ReaderT Z3Info Z3 a)
  deriving (Functor, Applicative, Monad, MonadReader Z3Info, MonadZ3, MonadIO)

-- dpairLookup :: (HEq f) => f t -> [DPair f g] -> Maybe (g t)
-- dpairLookup _ [] = Nothing
-- dpairLookup x (DPair ft gt:rest) =
--   case heq ft x of
--     Just Refl -> Just gt
--     Nothing -> dpairLookup x rest

-- newtype Z3Thing a = Z3Thing a

lookupZ3Name :: Z3Name -> Z3Converter FuncDecl
lookupZ3Name name = do
  xs <- fmap z3Info_assocs ask
  case lookup name xs of
    Just r -> pure r
    Nothing -> error $ "lookupZ3Name: Internal error: Cannot find name " ++ show name

lookupZ3Sort :: Z3Sort -> Z3Converter Sort
lookupZ3Sort s = do
  xs <- fmap z3Info_sorts ask
  case lookup s xs of
    Just r -> pure r
    Nothing -> error $ "lookupZ3Sort: Internal error: Cannot find sort " ++ show s

-- z3App :: Typeable a => Z3Name a -> [AST] -> Z3Converter (Z3 AST)
-- z3App name xs = do
--   z3Thing <- lookupZ3Name name
--   mkApp

mkAppM :: MonadZ3 z3 => FuncDecl -> [z3 AST] -> z3 AST
mkAppM decl = z3M (mkApp decl)

z3M :: MonadZ3 z3 => ([a] -> z3 b) -> [z3 a] -> z3 b
z3M f argsM =
  f =<< sequence argsM

lookupSetFamilyFn :: SetFamily -> Z3Converter (FuncDecl, [AST])
lookupSetFamilyFn (C_Exit' n) = do
  f <- lookupZ3Name Z3_C_Exit
  (f,) <$> sequence [toZ3 n]

lookupSetFamilyFn (C_Entry' n) = do
  f <- lookupZ3Name Z3_C_Entry
  (f,) <$> sequence [toZ3 n]

lookupSetFamilyFn (Atom_S' x y) = do
  f <- lookupZ3Name Z3_S
  (f,) <$> sequence [toZ3 x, toZ3 y]

lookupSetFamilyFn (Atom_E' x) = do
  f <- lookupZ3Name Z3_E
  (f,) <$> sequence [toZ3 x]

applyFamilyFnM :: SetFamily -> [Z3Converter AST] -> Z3Converter AST
applyFamilyFnM sf restArgs = do
  (sf, args) <- lookupSetFamilyFn sf
  mkAppM sf (map pure args ++ restArgs)

class Z3SetRelation a where
  applySetRelation :: a -> [AST] -> Z3Converter AST

  applySetRelationM :: a -> [Z3Converter AST] -> Z3Converter AST
  applySetRelationM sr xs = applySetRelation sr =<< sequence xs

instance Z3SetRelation SetFamily where
  applySetRelation sr = applyFamilyFnM sr . map pure
  applySetRelationM = applyFamilyFnM

instance Z3SetRelation AtomicSet where
  applySetRelation (SetFamily sr) args = applySetRelation sr args
  applySetRelation (SingleVar i) _ = toZ3 i

instance Z3SetRelation SetExpr where
  applySetRelation (SE_Atom sr) args = applySetRelation sr args
  applySetRelation (SE_Union x y) args = do
    z3M mkOr [applySetRelation x args, applySetRelation y args]
  applySetRelation (SE_UnionSingle x v s) args =
    applySetRelationM x [toZ3 v, toZ3 s]
  applySetRelation (SE_IfThenElse (sensX, sensY) t f) args = do
    z3_sensX <- toZ3 sensX
    z3_sensY <- toZ3 sensY

    eql <- mkEq z3_sensX z3_sensY

    join $ mkIte eql <$> applySetRelation t args <*> applySetRelation f args


class ToZ3 a where
  toZ3 :: a -> Z3Converter AST

-- instance ToZ3 SetFamily where
--   toZ3 (C_Exit' n) = do
--     z3_c_exit <- lookupZ3Name Z3_C_Exit
--     mkAppM z3_c_exit [toZ3 n]

--   toZ3 (C_Entry' n) = do
--     z3_c_entry <- lookupZ3Name Z3_C_Entry
--     mkAppM z3_c_entry [toZ3 n]

--   toZ3 (Atom_S' x y) = do
--     z3_s <- lookupZ3Name Z3_S
--     mkAppM z3_s [toZ3 x, toZ3 y]

--   toZ3 (Atom_E' x) = do
--     z3_e <- lookupZ3Name Z3_E
--     mkAppM z3_e [toZ3 x]

-- instance ToZ3 SetExpr where
--   toZ3 (Single n sens) = 

-- instance ToZ3 

mkSymVar :: String -> Z3Sort -> Z3Converter (Sort, Symbol, AST)
mkSymVar name z3sort = do
  sort <- lookupZ3Sort z3sort
  sym <- mkStringSymbol name
  var <- mkVar sym sort
  return (sort, sym, var)

instance ToZ3 NodeId where
  toZ3 n = join $ mkApp <$> lookupZ3Name (Z3_Node n) <*> pure []

instance ToZ3 Int where
  toZ3 n = join $ mkApp <$> lookupZ3Name (Z3_Var n) <*> pure []

instance ToZ3 SensExpr where
  toZ3 (SensAtom s) =
    join $ mkApp <$> (lookupZ3Name (Z3_Sens s)) <*> pure []

  toZ3 (Sens_T x y) = do
    z3_t <- lookupZ3Name Z3_T
    mkAppM z3_t [toZ3 x, toZ3 y]


instance ToZ3 SetConstraint where
  toZ3 (lhs :=: SE_Atom (SetFamily x)) = do

    (varSort, v_sym, v_var) <- mkSymVar "v" Var_Sort
    (sensSort, s_sym, s_var) <- mkSymVar "s" Sens_Sort

    mkForall [] [v_sym, s_sym] [ varSort, sensSort ]
      =<< join (mkEq <$> applyFamilyFnM lhs [pure v_var, pure s_var] <*> applyFamilyFnM x [pure v_var, pure s_var])

  toZ3 (lhs :=: SE_Union x y) = do
    (varSort, v_sym, v_var) <- mkSymVar "v" Var_Sort
    (sensSort, s_sym, s_var) <- mkSymVar "s" Sens_Sort
    let vs = [v_var, s_var]

    the_or <- z3M mkOr [applySetRelation x vs, applySetRelation y vs]

    mkForall [] [v_sym, s_sym] [ varSort, sensSort ]
      =<< join (mkEq <$> applySetRelation lhs vs <*> pure the_or)

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
      =<< (mkIte eql z3_t z3_f)

  --   join $ mkEq <$> toZ3 lhs <*> pure the_or

-- constraintToZ3 :: SetConstraint -> Z3 AST
-- constraintToZ3 (S_Entry x :=: S_Exit y) = do


constraintsToZ3 :: SetConstraints -> Z3Converter ()
constraintsToZ3 cs = do
  asts <- mapM undefined cs
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

main :: IO ()
main = do
  let fileName = "../test.c"

  stream <- readInputStream fileName

  case parseC stream (initPos fileName) of
    Left err -> error (show err)
    Right parsed -> do
      let parsed' = flip runState (NodeId 0) $ traverse (\x -> (x,) <$> newNodeId) parsed
          parsed'' = first (fmap snd) parsed'
          constraints = execConstraintGen $ transformM (constAction handleTransUnit) parsed''
          nodeInfo = map (nodeIdToLoc (fst parsed')) (getAnns (fst parsed''))

      putStrLn $ ppr constraints
      putStrLn (nodeIdLocInfo nodeInfo)
      print parsed'

