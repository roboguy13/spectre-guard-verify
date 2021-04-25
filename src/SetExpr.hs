{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

module SetExpr where

import           Control.Monad.State

import           Data.Data
import           Data.Kind
import           Data.Proxy
import           Data.Type.Bool
import           Data.Constraint

import           Ppr

import           Data.Set (Set)
import qualified Data.Set as Set

type family Sublist xs ys where
  Sublist (x:xs) (x:ys) = Sublist xs ys
  Sublist '[] ys = True
  Sublist xs ys = False

newtype NodeId = NodeId { getNodeId :: Integer }
  deriving (Show, Eq, Data, Ord)

newNodeId :: State NodeId NodeId
newNodeId = do
  NodeId x <- get

  put (NodeId (succ x))

  return $ NodeId x

instance Ppr NodeId where
  ppr = ('n':) . show . getNodeId

data Sensitivity = Public | Secret
  deriving (Show, Eq)

instance Ppr Sensitivity where ppr = show

data SensExpr
  = SensAtom Sensitivity
  | Sens_T NodeId
  deriving (Show)

instance Ppr SensExpr where
  ppr (SensAtom x) = ppr x
  ppr (Sens_T x) = "T(" ++ ppr x ++ ")"

type family In' x y where
  In' x (x : xs) = True
  In' x (y : xs) = In' x xs
  In' x '[] = False

type In x y = In' x y ~ True

type family Subset' xs ys where
  Subset' '[] ys = True
  Subset' (x:xs) ys = (x `In'` ys) && Subset' xs ys

type Subset xs ys = Subset' xs ys ~ True

type family Append xs ys where
  Append xs '[] = xs
  Append '[] ys = ys
  Append (x:xs) ys = x : Append xs ys

type family PairToList xs where
  PairToList (x, y) = Append (PairToList x) (PairToList y)
  PairToList x = (x : '[])

type family ListToPairs xs where
  ListToPairs (x : '[]) = x
  ListToPairs (x : xs) = (x, ListToPairs xs)

-- data DslVar dummy (a :: [Type]) where
data DslVar dummy a where
  DslVar :: dummy -> DslVar dummy a
  DslVar_Value :: a -> DslVar dummy a
  DslVar_Pair :: (DslVar dummy a, DslVar dummy b) -> DslVar dummy (a, b)
  -- DslVar_Value :: a -> DslVar dummy '[a]
  -- DslVar_Pair :: (a `Subset` xs, b `Subset` xs) => (DslVar dummy a, DslVar dummy b) -> DslVar dummy xs

data SetComprehension freeVars where
  SetComp' :: (NameFreeVars freeVars) => (forall dummy. DslVar dummy freeVars -> (DslVar dummy freeVars, CompPred (PairToList freeVars))) -> SetComprehension (PairToList freeVars)

-- data CompExpr freeVars where
--   CompExpr_Sens :: DslVar '[Sensitivity] -> CompExpr '[Sensitivity]
--   CompExpr_Pair :: DslVar '[Var, Sensitivity] -> CompExpr (Var, Sensitivity)

data CompPred freeVars where
  CompPred_PairIn :: (Var, Sensitivity) -> SetFamily freeVars -> CompPred '[Var, Sensitivity]
  CompPred_VarIn  :: Var -> SetFamily '[Var] -> CompPred '[Var]
  CompPred_And :: CompPred freeVarsA -> CompPred freeVarsB -> CompPred (Append freeVarsA freeVarsB)

data LatticeOp where
  LatticeJoin' :: (Ppr (ListToPairs freeVars)) => SetComprehension freeVars -> LatticeOp

data SetConstraint =
  forall freeVars.
    SetFamily freeVars :=: SetExpr freeVars

instance Ppr SetConstraint where
  ppr (x :=: y) = ppr x ++ " = " ++ ppr y

data Condition where
  SensEqual :: SensExpr -> SensExpr -> Condition
  PairIn :: (Int, Sensitivity) -> SetExpr freeVars -> Condition

data SetExpr (freeVars :: [*]) where
  SE_Atom :: AtomicSet freeVars -> SetExpr freeVars
  SE_Union :: AtomicSet freeVars -> SetExpr freeVars -> SetExpr freeVars
  SE_UnionSingle :: SetExpr freeVars -> Int -> SensExpr -> SetExpr freeVars
  SE_IfThenElse :: Condition -> SetExpr freeVars -> SetExpr freeVars -> SetExpr freeVars
  SE_Empty :: SetExpr freeVars
   -- Set comprehension:
  SE_Comp :: (Ppr (ListToPairs freeVars)) => SetComprehension freeVars -> SetExpr freeVars
  SE_LatticeOp :: LatticeOp -> SetExpr '[]

pattern SetComp x = SE_Comp (SetComp' x)
pattern LatticeJoin x = SE_LatticeOp (LatticeJoin' x)

instance Ppr Condition where
  ppr (SensEqual x y) = ppr x <> " = " <> ppr y
  ppr (PairIn p y) = ppr p <> " in " <> ppr y

instance Ppr (CompPred freeVars) where
  ppr (CompPred_PairIn p sf) = ppr p <> " in " <> ppr sf
  ppr (CompPred_VarIn v sf)  = show v <> " in " <> ppr sf
  ppr (CompPred_And x y)     = ppr x <> " \\/ " <> ppr y

instance Ppr Var where
  ppr v = show v

-- instance Ppr (SetComprehension freeVars) where
--   ppr (SetComp' x p) = "{ " <> ppr x <> " | " <> ppr p <> " }"

instance Ppr LatticeOp where
  ppr (LatticeJoin' x) = "U" <> ppr x

-- | For use in pretty printing
class Ppr freeVars => NameFreeVars freeVars where
  nameFreeVars :: proxy (PairToList freeVars) -> DslVar String freeVars

instance NameFreeVars (Var, Sensitivity) where
  nameFreeVars _ = DslVar_Pair (DslVar @_ @Var "v", DslVar @_ @Sensitivity "s")

instance NameFreeVars Sensitivity where
  nameFreeVars _ = DslVar "s"

type family PprList xs :: Constraint where
  PprList '[] = ()
  PprList (x : xs) = (Ppr x, PprList xs)

-- class x `In` xs => InC x xs
-- instance x `In` xs => InC x xs

-- type PprList xs = forall x. (x `InC` xs) :=> Ppr x

instance Ppr a => Ppr (DslVar String a) where
  ppr (DslVar str) = str
  ppr (DslVar_Value v) = ppr v

instance (Ppr a, Ppr b) => Ppr (DslVar String (a, b)) where
  ppr (DslVar str) = str
  ppr (DslVar_Value v) = ppr v
  ppr (DslVar_Pair p) = ppr p

instance (Ppr a, Ppr b) => Ppr (a, b) where
  ppr (x, y) = "(" <> ppr x <> ", " <> ppr y <> ")"

-- instance PprList freeVars => Ppr (DslVar String freeVars) where
  -- ppr (DslVar str) = str
  -- ppr (DslVar_Value v) = ppr v
  -- ppr (DslVar_Pair (x, y)) = "(" <> ppr x <> ", " <> ppr y <> ")"

-- instance forall freeVars. PprList freeVars => -- (forall x. (x `In` freeVars) :=> Ppr x) =>
--   Ppr (DslVar String freeVars) where
--     ppr (DslVar str) = str
--     ppr (DslVar_Value v) = undefined --ppr v

instance (Ppr (ListToPairs freeVars)) => Ppr (SetComprehension freeVars) where
  ppr sc@(SetComp' f) =
    let (x, p) = f (nameFreeVars (Proxy @freeVars)) --sc)
    in
    "{ " <> ppr x <> " | " <> ppr p <> " }"

instance Ppr (SetExpr freeVars) where
  ppr (SE_Atom x) = ppr x
  ppr (SE_Union x y) = ppr x ++ " U " ++ ppr y
  ppr (SE_UnionSingle x v s) = ppr x ++ " U {(" ++ show v ++ ", " ++ ppr s ++ ")}"
  ppr (SE_IfThenElse cond t f) = "if (" ++ ppr cond ++ ") then " ++ ppr t ++ " else " ++ ppr f
  ppr SE_Empty = "{}"
  ppr (SE_Comp x) = ppr x
  ppr (SE_LatticeOp x) = ppr x

type SetConstraints = [SetConstraint]

type Var = Int

data SetFamily freeVars where
  C_Exit' :: NodeId -> SetFamily '[Var, SensExpr]
  C_Entry' :: NodeId -> SetFamily '[Var, SensExpr]
  Atom_S' :: NodeId -> NodeId -> SetFamily '[Var, SensExpr]
  Atom_E' :: NodeId -> SetFamily '[Var]
  -- deriving (Show)


data AtomicSet freeVars where
  SetFamily :: SetFamily freeVars -> AtomicSet freeVars
  SingleVar :: Int -> AtomicSet '[Var]
  -- deriving (Show)

class ExprConstNames a where
  getVars :: a -> Set Int
  getNodeIds :: a -> Set NodeId
  getSPairs :: a -> Set (NodeId, NodeId)
  getTNodes :: a -> Set NodeId

instance ExprConstNames Condition where
  getVars (SensEqual x y) = getVars x <> getVars y
  getVars (PairIn _x y) = getVars y

  getNodeIds (SensEqual x y) = getNodeIds x <> getNodeIds y
  getNodeIds (PairIn _x y) = getNodeIds y

  getSPairs (SensEqual x y) = getSPairs x <> getSPairs y
  getSPairs (PairIn _x y) = getSPairs y

  getTNodes (SensEqual x y) = getTNodes x <> getTNodes y
  getTNodes (PairIn _x y) = getTNodes y

-- instance ExprConstNames (CompPred freeVars) where
--   getVars (CompPred_PairIn _p sf) = getVars sf
--   getVars (CompPred_VarIn  _v sf) = getVars sf
--   getVars (CompPred_And x y)      = getVars x <> getVars y

--   getSPairs (CompPred_PairIn _ sf) = getSPairs sf
--   getSPairs (CompPred_VarIn _ sf)  = getSPairs sf
--   getSPairs (CompPred_And x y) = getSPairs x <> getSPairs y

--   getTNodes (CompPred_PairIn _ sf) = getTNodes sf
--   getTNodes (CompPred_VarIn _ sf)  = getTNodes sf
--   getTNodes (CompPred_And x y) = getTNodes x <> getTNodes y

-- instance ExprConstNames (CompExpr freeVars) where
--   getVars _ = mempty
--   getVars _ = mempty
--   get

instance ExprConstNames SensExpr where
  getVars _ = mempty
  getNodeIds (SensAtom _) = mempty
  getNodeIds (Sens_T x) = Set.fromList [x]

  getSPairs _ = mempty

  getTNodes (Sens_T x) = Set.singleton x
  getTNodes _ = mempty

instance ExprConstNames (SetExpr freeVars) where
  getVars (SE_Atom x) = getVars x
  getVars (SE_Union x y) = getVars x <> getVars y
  getVars (SE_UnionSingle x v s) = getVars x <> Set.singleton v <> getVars s
  getVars (SE_IfThenElse cond x y) = getVars cond <> getVars x <> getVars y
  getVars SE_Empty = mempty

  getNodeIds (SE_Atom x) = getNodeIds x
  getNodeIds (SE_Union x y) = getNodeIds x <> getNodeIds y
  getNodeIds (SE_UnionSingle x v s) = getNodeIds x <> getNodeIds s
  getNodeIds (SE_IfThenElse cond x y) = getNodeIds cond <> getNodeIds x <> getNodeIds y
  getNodeIds SE_Empty = mempty

  getSPairs (SE_Atom x) = getSPairs x
  getSPairs (SE_Union x y) = getSPairs x <> getSPairs y
  getSPairs (SE_UnionSingle x v s) = getSPairs x <> getSPairs s
  getSPairs (SE_IfThenElse cond x y) = getSPairs cond <> getSPairs x <> getSPairs y
  getSPairs SE_Empty = mempty

  getTNodes (SE_Atom x) = getTNodes x
  getTNodes (SE_Union x y) = getTNodes x <> getTNodes y
  getTNodes (SE_UnionSingle x v s) = getTNodes x <> getTNodes s
  getTNodes (SE_IfThenElse cond x y) = getTNodes cond <> getTNodes x <> getTNodes y
  getTNodes SE_Empty = mempty


instance ExprConstNames (AtomicSet freeVars) where
  getVars (SetFamily sf) = getVars sf
  getVars (SingleVar v) = Set.singleton v

  getNodeIds (SetFamily sf) = getNodeIds sf
  getNodeIds (SingleVar _) = mempty

  getSPairs (SetFamily sf) = getSPairs sf
  getSPairs _ = mempty

  getTNodes (SetFamily sf) = getTNodes sf
  getTNodes _ = mempty

instance ExprConstNames (SetFamily freeVars) where
  getVars _ = mempty
  getNodeIds (C_Exit' x) = Set.singleton x
  getNodeIds (C_Entry' x) = Set.singleton x
  getNodeIds (Atom_S' x y) = Set.fromList [x, y]
  getNodeIds (Atom_E' x) = Set.singleton x

  getSPairs (Atom_S' x y) = Set.singleton (x, y)
  getSPairs _ = mempty

  getTNodes _ = mempty

instance ExprConstNames SetConstraint where
  getVars (x :=: y) = getVars x <> getVars y
  getNodeIds (x :=: y) = getNodeIds x <> getNodeIds y
  getSPairs (x :=: y) = getSPairs x <> getSPairs y
  getTNodes (x :=: y) = getTNodes x <> getTNodes y

instance ExprConstNames SetConstraints where
  getVars = foldr Set.union mempty . map getVars
  getNodeIds = foldr Set.union mempty . map getNodeIds
  getSPairs = foldr Set.union mempty . map getSPairs
  getTNodes = foldr Set.union mempty . map getTNodes

pattern C_Exit x = SetFamily (C_Exit' x)
pattern C_Entry x = SetFamily (C_Entry' x)
pattern Atom_S x y = SetFamily (Atom_S' x y)
pattern Atom_E x = SetFamily (Atom_E' x)

instance Ppr (AtomicSet freeVars) where
  ppr (SetFamily x) = ppr x
  -- ppr (Single x y) = "{(" ++ show x ++ ", " ++ ppr y ++ ")}"
  ppr (SingleVar v) = "{" ++ show v ++ "}"

instance Ppr (SetFamily freeVars) where
  ppr (C_Exit' n) = "C_exit(" ++ ppr n ++ ")"
  ppr (C_Entry' n) = "C_entry(" ++ ppr n ++ ")"
  ppr (Atom_S' x y) = "S(" ++ ppr x ++ ", " ++ ppr y ++ ")"
  ppr (Atom_E' x) = "E(" ++ ppr x ++ ")"

instance Ppr SetConstraints where
  ppr = unlines . map ppr

class SetFamilyExpr f where
  c_exit :: NodeId -> f '[Var, SensExpr]
  c_entry :: NodeId -> f '[Var, SensExpr]
  atom_s :: NodeId -> NodeId -> f '[Var, SensExpr]
  atom_e :: NodeId -> f '[Var]


class SetFamilyExpr f => SetExprAtom f where
  -- single :: Int -> SensExpr -> a
  singleVar :: Int -> f '[Var]

instance SetFamilyExpr SetFamily where
  c_exit = C_Exit'
  c_entry = C_Entry'
  atom_s = Atom_S'
  atom_e = Atom_E'

instance SetFamilyExpr AtomicSet where
  c_exit = C_Exit
  c_entry = C_Entry
  atom_s = Atom_S
  atom_e = Atom_E


instance SetExprAtom AtomicSet where
  -- single = Single
  singleVar = SingleVar

instance SetFamilyExpr SetExpr where
  c_exit = SE_Atom . c_exit
  c_entry = SE_Atom . c_entry
  atom_s x y = SE_Atom (atom_s x y)
  atom_e = SE_Atom . atom_e

instance SetExprAtom SetExpr where
  -- single x y = SE_Atom (single x y)
  singleVar = SE_Atom . singleVar

