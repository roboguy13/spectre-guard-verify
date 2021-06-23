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

import           Ppr
import           Pattern

class Unconstrained (a :: k)
instance Unconstrained a

class BoolExpr repr where
  type EqualCt repr :: * -> Constraint

  in_ :: (SetExpr repr, SetCt repr set) => repr a -> repr (set a) -> repr Bool
  (^&&^) :: repr Bool -> repr Bool -> repr Bool
  equal :: EqualCt repr a => repr a -> repr a -> repr Bool

  true :: repr Bool
  false :: repr Bool

  ite :: repr Bool -> repr a -> repr a -> repr a

class SetExpr repr where
  type SetCt repr :: (* -> *) -> Constraint
  type SetElemCt repr :: * -> Constraint

  union :: (SetCt repr set, SetElemCt repr a) => repr (set a) -> repr (set a) -> repr (set a)
  unionSingle :: (SetCt repr set, SetElemCt repr a) => repr (set a) -> repr a -> repr (set a)
  empty :: (SetCt repr set, SetElemCt repr a) => repr (set a)

  setCompr :: (SetCt repr set, SetElemCt repr a, SetElemCt repr b) => (repr a -> repr b) -> (repr a -> repr Bool) -> repr (set a) -> repr (set b)

class LatticeExpr repr where
  type LatticeCt repr :: * -> Constraint

  lub :: (SetExpr repr, SetCt repr set, LatticeCt repr a) => repr (set a) -> repr a

class Value repr where
  type ValueCt repr :: * -> Constraint

  value :: ValueCt repr a => a -> repr a

type Expr repr = (BoolExpr repr, SetExpr repr, LatticeExpr repr, Value repr)

data ConstraintE repr where
  (:=:) :: {- (Expr repr) => -} repr a -> repr a -> ConstraintE repr

