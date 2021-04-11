{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}


module SetExpr where

import           Control.Monad.State

import           Data.Data

import           Ppr

newtype NodeId = NodeId { getNodeId :: Integer }
  deriving (Show, Eq, Data)

newNodeId :: State NodeId NodeId
newNodeId = do
  NodeId x <- get

  put (NodeId (succ x))

  return $ NodeId x

instance Ppr NodeId where
  ppr = ('n':) . show . getNodeId

data Sensitivity = Public | Secret
  deriving (Show)

instance Ppr Sensitivity where ppr = show

data SensExpr
  = SensAtom Sensitivity
  | Sens_T NodeId NodeId
  deriving (Show)

instance Ppr SensExpr where
  ppr (SensAtom x) = ppr x
  ppr (Sens_T x y) = "T(" ++ ppr x ++ ", " ++ ppr y ++ ")"

data SetConstraint =
  AtomicSet :=: SetExpr
  deriving (Show)

instance Ppr SetConstraint where
  ppr (x :=: y) = ppr x ++ " = " ++ ppr y

data SetExpr
  = SE_Atom AtomicSet
  | SE_Union SetExpr SetExpr
  | SE_IfThenElse (SensExpr, SensExpr) SetExpr SetExpr
  deriving (Show)

instance Ppr SetExpr where
  ppr (SE_Atom x) = ppr x
  ppr (SE_Union x y) = ppr x ++ " U " ++ ppr y
  ppr (SE_IfThenElse (x,y) t f) = "if (" ++ ppr x ++ " = " ++ ppr y ++ ") then " ++ ppr t ++ " else " ++ ppr f

type SetConstraints = [SetConstraint]

data AtomicSet
  = C_Exit NodeId
  | C_Entry NodeId
  | Atom_S NodeId NodeId
  | Atom_E NodeId
  | Single Int SensExpr
  | SingleVar Int
  deriving (Show)

instance Ppr AtomicSet where
  ppr (C_Exit n) = "C_exit(" ++ ppr n ++ ")"
  ppr (C_Entry n) = "C_entry(" ++ ppr n ++ ")"
  ppr (Atom_S x y) = "S(" ++ ppr x ++ ", " ++ ppr y ++ ")"
  ppr (Atom_E x) = "E(" ++ ppr x ++ ")"
  ppr (Single x y) = "{(" ++ show x ++ ", " ++ ppr y ++ ")}"
  ppr (SingleVar v) = show v

instance Ppr SetConstraints where
  ppr = unlines . map ppr

class SetExprAtom a where
  c_exit :: NodeId -> a
  c_entry :: NodeId -> a
  atom_s :: NodeId -> NodeId -> a
  atom_e :: NodeId -> a
  single :: Int -> SensExpr -> a
  singleVar :: Int -> a

instance SetExprAtom AtomicSet where
  c_exit = C_Exit
  c_entry = C_Entry
  atom_s = Atom_S
  atom_e = Atom_E
  single = Single
  singleVar = SingleVar

instance SetExprAtom SetExpr where
  c_exit = SE_Atom . c_exit
  c_entry = SE_Atom . c_entry
  atom_s x y = SE_Atom (atom_s x y)
  atom_e = SE_Atom . atom_e
  single x y = SE_Atom (single x y)
  singleVar = SE_Atom . singleVar

