{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}

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
  SetFamily :=: SetExpr
  deriving (Show)

instance Ppr SetConstraint where
  ppr (x :=: y) = ppr x ++ " = " ++ ppr y

data SetExpr
  = SE_Atom AtomicSet
  | SE_Union AtomicSet AtomicSet
  | SE_UnionSingle SetExpr Int SensExpr
  | SE_IfThenElse (SensExpr, SensExpr) SetExpr SetExpr
  deriving (Show)

instance Ppr SetExpr where
  ppr (SE_Atom x) = ppr x
  ppr (SE_Union x y) = ppr x ++ " U " ++ ppr y
  ppr (SE_UnionSingle x v s) = ppr x ++ " U {(" ++ show v ++ ", " ++ ppr s ++ ")}"
  ppr (SE_IfThenElse (x,y) t f) = "if (" ++ ppr x ++ " = " ++ ppr y ++ ") then " ++ ppr t ++ " else " ++ ppr f

type SetConstraints = [SetConstraint]

data SetFamily =
    C_Exit' NodeId
  | C_Entry' NodeId
  | Atom_S' NodeId NodeId
  | Atom_E' NodeId
  deriving (Show)


data AtomicSet
  = SetFamily SetFamily
  -- | Single Int SensExpr
  | SingleVar Int
  deriving (Show)

class ExprConstNames a where
  getVars :: a -> [Int]
  getNodeIds :: a -> [NodeId]

instance ExprConstNames SensExpr where
  getVars _ = []
  getNodeIds (SensAtom _) = []
  getNodeIds (Sens_T x y) = [x, y]

instance ExprConstNames SetExpr where
  getVars (SE_Atom x) = getVars x
  getVars (SE_Union x y) = getVars x ++ getVars y
  getVars (SE_UnionSingle x v s) = getVars x ++ [v] ++ getVars s
  getVars (SE_IfThenElse (sA, sB) x y) = getVars sA ++ getVars sB ++ getVars x ++ getVars y

  getNodeIds (SE_Atom x) = getNodeIds x
  getNodeIds (SE_Union x y) = getNodeIds x ++ getNodeIds y
  getNodeIds (SE_UnionSingle x v s) = getNodeIds x ++ getNodeIds s
  getNodeIds (SE_IfThenElse (sA, sB) x y) = getNodeIds sA ++ getNodeIds sB ++ getNodeIds x ++ getNodeIds y

instance ExprConstNames AtomicSet where
  getVars (SetFamily sf) = getVars sf
  getVars (SingleVar v) = [v]

  getNodeIds (SetFamily sf) = getNodeIds sf
  getNodeIds (SingleVar _) = []

instance ExprConstNames SetFamily where
  getVars _ = []
  getNodeIds (C_Exit' x) = [x]
  getNodeIds (C_Entry' x) = [x]
  getNodeIds (Atom_S' x y) = [x, y]
  getNodeIds (Atom_E' x) = [x]

instance ExprConstNames SetConstraint where
  getVars (x :=: y) = getVars x ++ getVars y
  getNodeIds (x :=: y) = getNodeIds x ++ getNodeIds y

instance ExprConstNames SetConstraints where
  getVars = concatMap getVars
  getNodeIds = concatMap getNodeIds

pattern C_Exit x = SetFamily (C_Exit' x)
pattern C_Entry x = SetFamily (C_Entry' x)
pattern Atom_S x y = SetFamily (Atom_S' x y)
pattern Atom_E x = SetFamily (Atom_E' x)

instance Ppr AtomicSet where
  ppr (SetFamily x) = ppr x
  -- ppr (Single x y) = "{(" ++ show x ++ ", " ++ ppr y ++ ")}"
  ppr (SingleVar v) = show v

instance Ppr SetFamily where
  ppr (C_Exit' n) = "C_exit(" ++ ppr n ++ ")"
  ppr (C_Entry' n) = "C_entry(" ++ ppr n ++ ")"
  ppr (Atom_S' x y) = "S(" ++ ppr x ++ ", " ++ ppr y ++ ")"
  ppr (Atom_E' x) = "E(" ++ ppr x ++ ")"

instance Ppr SetConstraints where
  ppr = unlines . map ppr

class SetFamilyExpr a where
  c_exit :: NodeId -> a
  c_entry :: NodeId -> a
  atom_s :: NodeId -> NodeId -> a
  atom_e :: NodeId -> a


class SetFamilyExpr a => SetExprAtom a where
  -- single :: Int -> SensExpr -> a
  singleVar :: Int -> a

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

