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

import           Ppr
import           Pattern

import           Data.Set (Set)
import qualified Data.Set as Set

class ConstraintE p where
  (.=.) :: forall c f a. c a => f a -> p c f a -> SomeConstraint c f

instance ConstraintE SetExpr where
  x .=. y = SetConstraint (SetConstr x y)

instance ConstraintE LatticeExpr where
  x .=. y = LatticeConstraint (LatticeConstr x y)

class InterpretConstraint p f i where
  interpretC :: p c f -> i

data SomeConstraint c f where
  LatticeConstraint :: LatticeConstraint c f -> SomeConstraint c f
  SetConstraint     :: SetConstraint c f     -> SomeConstraint c f

interpretConstraints :: forall c f i. (InterpretConstraint LatticeConstraint f i, InterpretConstraint SetConstraint f i, Monoid i) => [SomeConstraint c f] -> i
interpretConstraints = foldMap interpretSC
  where
    interpretSC :: SomeConstraint c f -> i
    interpretSC (LatticeConstraint c) = interpretC c
    interpretSC (SetConstraint c) = interpretC c

-- class Interpret a b where
--   interpret :: LamVar a r -> r

-- class Subst a b where
--   subst :: a -> LamVar a b -> b

data SetConstraint c f =
  forall a. c a =>
    SetConstr (f a) (SetExpr c f a)

data LatticeConstraint c f =
  forall a. c a =>
    LatticeConstr (f a) (LatticeExpr c f a)

data LamVar a r = LamVar r

-- class Repr f a where
--   type ReprM f a :: * -> *
--   repr :: ReprM f a (f a)

-- type family ReprFC (f :: * -> *) a :: Constraint
-- type family ReprC a :: Constraint

-- type family Convert (f :: * -> *) a :: Constraint

-- class Convert t a | t -> a where
--   type family Converter t a :: * -> *
--   type family ConvertType t a = r | r -> t
--   convert :: a -> Converter t a (ConvertType t a)
--   mkVar :: Converter t a (t a)


data Lam c t where
  Lam :: forall c a b. c a => (forall f. LamVar a (f a) -> b) -> Lam c (a -> b)

-- lamRepr :: forall f a b. Repr f a => (LamVar a (f a) -> b) -> ReprM f a (f a)
-- lamRepr _ = repr

-- pattern WithConvert :: forall t a. (Convert t a => a) -> a
-- pattern WithConvert x = LiftedValue x

data Lifted c a where
  LiftedValue :: c a => a -> Lifted c a
  LiftedVar :: LamVar a (f a) -> Lifted c a

data BoolExpr (c :: * -> Constraint) (f :: * -> *) where
  In :: c a => Lifted c a -> SetExpr c f a -> BoolExpr c f
  (:&&:) :: BoolExpr c f -> BoolExpr c f -> BoolExpr c f
  LatticeEqual :: LatticeExpr c f a -> LatticeExpr c f a -> BoolExpr c f

-- in_ :: ReprC f a => (forall t. Convert t a => Converter t a (ConvertType t a)) -> SetExpr f a -> BoolExpr f
-- in_ x xs = In (LiftedValue x) xs


-- pattern In' :: Convert f a =>
--      -- forall (t :: * -> *).
--      --  Convert t a =>
--       a
--      -> SetExpr f a -> BoolExpr f
pattern In' x xs = In (LiftedValue x) xs

-- in' x xs = In (LiftedValue x) xs

data SetExpr (c :: * -> Constraint) (f :: * -> *) a where
  SetFamily :: f a -> SetExpr c f a
  SetUnion :: SetExpr c f a -> SetExpr c f a -> SetExpr c f a
  SetUnionSingle :: c a => SetExpr c f a -> a -> SetExpr c f a
  SetCompr :: {- ReprC f a => -} Lam c (a -> SetExpr c f b) -> Lam c (a -> BoolExpr c f) -> SetExpr c f a -> SetExpr c f b
  SetIte :: BoolExpr c f -> SetExpr c f a -> SetExpr c f a -> SetExpr c f a
  SetEmpty :: SetExpr c f a
  -- SetUnlamVar :: LamVar a r -> SetExpr f a

data LatticeExpr c f a where
  LatticeVal ::  {- ReprC f a => -} Lifted c a -> LatticeExpr c f a
  Lub :: SetExpr c f a -> LatticeExpr c f a
  LatticeIte :: BoolExpr c f -> LatticeExpr c f a -> LatticeExpr c f a -> LatticeExpr c f a

pattern LatticeVal' x = LatticeVal (LiftedValue x)

-- latticeVal' x = LatticeVal (LiftedValue x)

class Ite p where
  ite :: BoolExpr c f -> p c f a -> p c f a -> p c f a

instance Ite SetExpr where
  ite = SetIte

instance Ite LatticeExpr where
  ite = LatticeIte

