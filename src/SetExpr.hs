{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

module SetExpr where

import           Control.Monad.State

import           Data.Data

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
  | Sens_T NodeId NodeId
  deriving (Show)

instance Ppr SensExpr where
  ppr (SensAtom x) = ppr x
  ppr (Sens_T x y) = "T(" ++ ppr x ++ ", " ++ ppr y ++ ")"

data SetConstraint =
  forall freeVars.
      -- freeVarsLHS `Sublist` freeVarsRHS ~ True =>
        SetFamily freeVars :=: SetExpr freeVars
  -- deriving (Show)

instance Ppr SetConstraint where
  ppr (x :=: y) = ppr x ++ " = " ++ ppr y

data SetExpr (freeVars :: [*]) where
  SE_Atom :: AtomicSet freeVars -> SetExpr freeVars
  SE_Union :: AtomicSet freeVars -> SetExpr freeVars -> SetExpr freeVars
  SE_UnionSingle :: SetExpr freeVars -> Int -> SensExpr -> SetExpr freeVars
  SE_IfThenElse :: (SensExpr, SensExpr) -> SetExpr freeVars -> SetExpr freeVars -> SetExpr freeVars
  SE_Empty :: SetExpr freeVars
  -- deriving (Show)

instance Ppr (SetExpr freeVars) where
  ppr (SE_Atom x) = ppr x
  ppr (SE_Union x y) = ppr x ++ " U " ++ ppr y
  ppr (SE_UnionSingle x v s) = ppr x ++ " U {(" ++ show v ++ ", " ++ ppr s ++ ")}"
  ppr (SE_IfThenElse (x,y) t f) = "if (" ++ ppr x ++ " = " ++ ppr y ++ ") then " ++ ppr t ++ " else " ++ ppr f
  ppr SE_Empty = "{}"

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
  getTPairs :: a -> Set (NodeId, NodeId)

instance ExprConstNames SensExpr where
  getVars _ = mempty
  getNodeIds (SensAtom _) = mempty
  getNodeIds (Sens_T x y) = Set.fromList [x, y]

  getSPairs _ = mempty

  getTPairs (Sens_T x y) = Set.singleton (x, y)
  getTPairs _ = mempty

instance ExprConstNames (SetExpr freeVars) where
  getVars (SE_Atom x) = getVars x
  getVars (SE_Union x y) = getVars x <> getVars y
  getVars (SE_UnionSingle x v s) = getVars x <> Set.singleton v <> getVars s
  getVars (SE_IfThenElse (sA, sB) x y) = getVars sA <> getVars sB <> getVars x <> getVars y
  getVars SE_Empty = mempty

  getNodeIds (SE_Atom x) = getNodeIds x
  getNodeIds (SE_Union x y) = getNodeIds x <> getNodeIds y
  getNodeIds (SE_UnionSingle x v s) = getNodeIds x <> getNodeIds s
  getNodeIds (SE_IfThenElse (sA, sB) x y) = getNodeIds sA <> getNodeIds sB <> getNodeIds x <> getNodeIds y
  getNodeIds SE_Empty = mempty

  getSPairs (SE_Atom x) = getSPairs x
  getSPairs (SE_Union x y) = getSPairs x <> getSPairs y
  getSPairs (SE_UnionSingle x v s) = getSPairs x <> getSPairs s
  getSPairs (SE_IfThenElse (sA, sB) x y) = getSPairs sA <> getSPairs sB <> getSPairs x <> getSPairs y
  getSPairs SE_Empty = mempty

  getTPairs (SE_Atom x) = getTPairs x
  getTPairs (SE_Union x y) = getTPairs x <> getTPairs y
  getTPairs (SE_UnionSingle x v s) = getTPairs x <> getTPairs s
  getTPairs (SE_IfThenElse (sA, sB) x y) = getTPairs sA <> getTPairs sB <> getTPairs x <> getTPairs y
  getTPairs SE_Empty = mempty


instance ExprConstNames (AtomicSet freeVars) where
  getVars (SetFamily sf) = getVars sf
  getVars (SingleVar v) = Set.singleton v

  getNodeIds (SetFamily sf) = getNodeIds sf
  getNodeIds (SingleVar _) = mempty

  getSPairs (SetFamily sf) = getSPairs sf
  getSPairs _ = mempty

  getTPairs (SetFamily sf) = getTPairs sf
  getTPairs _ = mempty

instance ExprConstNames (SetFamily freeVars) where
  getVars _ = mempty
  getNodeIds (C_Exit' x) = Set.singleton x
  getNodeIds (C_Entry' x) = Set.singleton x
  getNodeIds (Atom_S' x y) = Set.fromList [x, y]
  getNodeIds (Atom_E' x) = Set.singleton x

  getSPairs (Atom_S' x y) = Set.singleton (x, y)
  getSPairs _ = mempty

  getTPairs _ = mempty

instance ExprConstNames SetConstraint where
  getVars (x :=: y) = getVars x <> getVars y
  getNodeIds (x :=: y) = getNodeIds x <> getNodeIds y
  getSPairs (x :=: y) = getSPairs x <> getSPairs y
  getTPairs (x :=: y) = getTPairs x <> getTPairs y

instance ExprConstNames SetConstraints where
  getVars = foldr Set.union mempty . map getVars
  getNodeIds = foldr Set.union mempty . map getNodeIds
  getSPairs = foldr Set.union mempty . map getSPairs
  getTPairs = foldr Set.union mempty . map getTPairs

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

