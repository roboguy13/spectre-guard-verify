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
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilyDependencies #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

module SetExpr where

import           Control.Monad.State
import           Control.Monad.Identity

import           Data.Data
import           Data.Kind
import           Data.Proxy
import           Data.Type.Bool
import           Data.Constraint
import           Data.Semigroup

import           Data.Set (Set)

import           Ppr
import           Pattern

data SetE a

class ElemVal r where
  type ElemRepr r :: * -> Constraint

-- instance ElemVal f => ElemVal (SetE f) where
--   type ElemRepr (SetE a) = ElemRepr f
--   elemRepr _ = elemRepr (Proxy @a)

data Expr r base m f t where
  SetFamily :: f x (Set a) -> Expr r base m f (Set a)
  BaseVal :: base -> Expr r base m f a
  MonoidVal :: m -> Expr r base m f m
  BoolVal :: Bool -> Expr r base m f Bool

  VarRepr :: r -> Expr r base m f a -- For use in representing lambdas

  Pair :: Expr r base m f a -> Expr r base m f b -> Expr r base m f (a, b)
  Fst :: Expr r base m f (a, b) -> Expr r base m f a
  Snd :: Expr r base m f (a, b) -> Expr r base m f b

  In :: Expr r base m f a -> Expr r base m f (Set a) -> Expr r base m f Bool
  And :: Expr r base m f Bool -> Expr r base m f Bool -> Expr r base m f Bool
  BaseEqual :: Expr r base m f base -> Expr r base m f base -> Expr r base m f Bool
  MonoidEqual :: Expr r base m f m -> Expr r base m f m -> Expr r base m f Bool
  Ite :: Expr r base m f Bool -> Expr r base m f a -> Expr r base m f a -> Expr r base m f a

  Union :: Expr r base m f (Set a) -> Expr r base m f (Set a) -> Expr r base m f (Set a)
  UnionSingle :: Expr r base m f (Set a) -> Expr r base m f a -> Expr r base m f (Set a)
  Empty :: (ElemVal r, ElemRepr r a) => Expr r base m f (Set a)

  SetCompr :: (ElemVal r, ElemRepr r a, ElemRepr r b) => (forall r. Expr r base m f a -> Expr r base m f b) -> (forall r. Expr r base m f a -> Expr r base m f Bool) -> Expr r base m f (Set a) -> Expr r base m f (Set b)

  Lub :: Expr r base m f (Set m) -> Expr r base m f m

-- class ExprEq a

class Value e v where
  value :: v -> e

instance Value (Expr r base m f base) base where value = BaseVal
instance Value (Expr r base m f m) m where value = MonoidVal
instance Value (Expr r base m f (Set a)) (f x (Set a)) where value = SetFamily
instance Value (Expr r base m f Bool) Bool where value = BoolVal
instance (Value (Expr r base m f a) a, Value (Expr r base m f b) b) => Value (Expr r base m f (a, b)) (a, b) where
  value (x, y) = Pair (value x) (value y)

-- pairVal :: (a, b) -> Expr r base m f (a, b)
-- pairVal = uncurry Pair


data ConstraintE r base m f where
  (:=:) :: Expr r base m f a -> Expr r base m f a -> ConstraintE r base m f

  -- | (Non-strict) subset relation constraint
  (:>:) :: Expr r base m f (Set a) -> Expr r base m f (Set a) -> ConstraintE r base m f

data ConstraintType = EqualityConstraint | SubsetConstraint

constraintType :: ConstraintE r base m f -> ConstraintType
constraintType (_ :=: _) = EqualityConstraint
constraintType (_ :>: _) = SubsetConstraint

withConstraintSides :: ConstraintE r base m f -> (forall x. (Expr r base m f x, Expr r base m f x) -> b) -> b
withConstraintSides (x :=: y) k = k (x, y)
withConstraintSides (x :>: y) k = k (x, y)

-- class Unconstrained (a :: k)
-- instance Unconstrained a

-- class BoolExpr repr where
--   type EqualCt repr :: * -> Constraint

--   in_ :: (SetExpr repr, SetCt repr set) => repr a -> repr (set a) -> repr Bool
--   (^&&^) :: repr Bool -> repr Bool -> repr Bool
--   equal :: EqualCt repr a => repr a -> repr a -> repr Bool

--   true :: repr Bool
--   false :: repr Bool

--   ite :: repr Bool -> repr a -> repr a -> repr a

-- class SetExpr repr where
--   type SetCt repr :: (* -> *) -> Constraint
--   type SetElemCt repr :: * -> Constraint

--   union :: (SetCt repr set, SetElemCt repr a) => repr (set a) -> repr (set a) -> repr (set a)
--   unionSingle :: (SetCt repr set, SetElemCt repr a) => repr (set a) -> repr a -> repr (set a)
--   empty :: (SetCt repr set, SetElemCt repr a) => repr (set a)

--   setCompr :: (SetCt repr set, SetElemCt repr a, SetElemCt repr b) => (repr a -> repr b) -> (repr a -> repr Bool) -> repr (set a) -> repr (set b)

-- class LatticeExpr repr where
--   type LatticeCt repr :: * -> Constraint

--   lub :: (SetExpr repr, SetCt repr set, LatticeCt repr a) => repr (set a) -> repr a

-- class Value repr where
--   type ValueCt repr :: * -> Constraint

--   value :: ValueCt repr a => a -> repr a

-- type Expr repr = (BoolExpr repr, SetExpr repr, LatticeExpr repr, Value repr)

-- data ConstraintE repr where
--   (:=:) :: {- (Expr repr) => -} repr a -> repr a -> ConstraintE repr

