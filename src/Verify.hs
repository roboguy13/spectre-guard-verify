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
{-# LANGUAGE TemplateHaskell #-}

{-# LANGUAGE QuantifiedConstraints #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

import           Language.C
import           Language.C.System.Preprocess
import           Language.C.System.GCC
import           Language.C.Data.Ident

import           System.FilePath.Posix
import           System.Process
import           System.IO

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
import           Data.Functor.Apply

import qualified Data.ByteString as BS

import           Data.Maybe (maybeToList)

import qualified Data.List as L
import qualified Data.Set as Set

import           Data.Set (Set)

-- import           Lens.Micro
-- import           Lens.Micro.TH

import           Control.Monad.ST
import           Data.STRef
import           Control.Monad.ST.Class

import           Orphans ()
import           Ppr
import           SetExpr
import           Pattern
import           ConstraintGen
-- import           DOT
import           Propagator
-- import           ValidNodeId

generateDOT :: Bool
generateDOT = True

data VerifyInfo s =
  VerifyInfo
    { verifyInfoCEntry :: IxedCell s NodeId (Set (Var, SensExpr))
    , verifyInfoCExit :: IxedCell s NodeId (Set (Var, SensExpr))
    , verifyInfoE :: IxedCell s NodeId (Set Var)
    , verifyInfoT :: IxedCell s NodeId SensExpr
    , verifyInfoS :: IxedCell s (NodeId, NodeId) (Set (Var, SensExpr))
    }

getSetFamily' :: VerifyInfo s -> AnalysisSetFamily a b -> (a, IxedCell s a b)
getSetFamily' vi (C_Entry n) = (n, verifyInfoCEntry vi)
getSetFamily' vi (C_Exit  n) = (n, verifyInfoCExit  vi)
getSetFamily' vi (S_Family m n) = ((m, n), verifyInfoS vi)
getSetFamily' vi (E_Family n) = (n, verifyInfoE vi)
getSetFamily' vi (B_Family {}) = error "getSetFamily: B_Family"



-- | c1(x) U c2(y) = rhs(z)
unionAt :: (Ord x, Ord y, Ord z, Ord a) => x -> y -> z -> IxedCell s x (Set a) -> IxedCell s y (Set a) -> IxedCell s z (Set a) -> ST s ()
unionAt x y z c1 c2 rhs = do
  binaryAt2 x y z Set.union c1 c2 rhs
  -- TODO: Should there be reverse operations?

emptySetAt :: (Ord a, Ord b) => a -> ST s (IxedCell s a (Set b))
emptySetAt x = knownAt (x, mempty)

unionSingleAt :: (Ord a, Ord b) => a -> b -> IxedCell s a (Set b) -> IxedCell s a (Set b) -> ST s ()
unionSingleAt x y c1 rhs =
  unaryAt x (Set.insert y) c1 rhs
  -- TODO: Should there be reverse operations?

data VerifyError = VerifyInconsistency String
  deriving (Show)

data VerifyResult = Correct | Incorrect [String]
  deriving (Show)

instance Semigroup VerifyResult where
  Incorrect xs <> Incorrect ys = Incorrect (xs <> ys)
  Correct <> Correct           = Correct
  Incorrect xs <> _            = Incorrect xs
  _ <> Incorrect ys            = Incorrect ys

instance Monoid VerifyResult where
  mempty = Correct

newtype Verify s a = Verify (StateT (VerifyInfo s) (ST s) a)
  deriving (Functor, Applicative, Monad, MonadState (VerifyInfo s), MonadST)

getSetFamily :: AnalysisSetFamily a b -> Verify s (a, IxedCell s a b)
getSetFamily sf = (`getSetFamily'` sf) <$> get

data Store s b = forall a. Ord a => MkStore a (IxedCell s a b)

infixl 4 .$.
(.$.) :: (a -> b) -> Store s a -> Verify s (Defined b)
f .$. MkStore x c = liftST (fmap f <$> readIxedCellAt c x)

infixl 4 .*.
(.*.) :: Eq b => Verify s (Defined (a -> b)) -> Store s a -> Verify s (Defined b)
fM .*. MkStore x c = do
  fM >>= \case
    Known f -> f .$. MkStore x c
    Unknown -> pure Unknown
    Inconsistent -> pure Inconsistent


-- instance Apply (Store s) where
--   MkStore xF f <*> MkStore xC c =

readStore :: Store s b -> ST s (Defined b)
readStore (MkStore x c) = readIxedCellAt c x

constStore :: b -> Verify s (Store s b)
constStore x = liftST (MkStore () <$> known x)

-- constDefinedStore :: Defined b -> Verify s (Store b)
-- constDefinedStore d = liftST (MkStore () <$> 

evalSensExpr :: SensExpr -> Verify s (Store s SensExpr)
evalSensExpr (SensAtom s) = constStore (SensAtom s)
evalSensExpr (SensT n) = MkStore n . verifyInfoT <$> get

-- type AnalysisExpr' s = AnalysisExpr (Store s)

evalUnary :: (Eq a, Eq b, Eval f, Ord a) =>
   (a -> b) -> f a -> Verify s (Store s b)
evalUnary f x = do
  MkStore xPoint x' <- eval x
  r <- liftST unknown
  liftST $ unaryAt2 xPoint () f x' r
  return (MkStore () r)


evalBinary :: (Eq b, Eq c, Eval f, Eval g, Ord a) =>
   (a -> b -> c) -> f a -> g b -> Verify s (Store s c)
evalBinary f x y = do
  MkStore xPoint x' <- eval x
  MkStore yPoint y' <- eval y
  r <- liftST unknown
  liftST $ binaryAt2 xPoint yPoint () f x' y' r
  return (MkStore () r)

evalTrinary :: (Ord a, Eq b, Eq c, Eq d, Eval f, Eval g, Eval h) =>
  (a -> b -> c -> d) -> f a -> g b -> h c -> Verify s (Store s d)
evalTrinary f x y z = do
  MkStore xPoint x' <- eval x
  MkStore yPoint y' <- eval y
  MkStore zPoint z' <- eval z
  r <- liftST unknown


class Eval f where
  eval :: f t -> Verify s (Store s t)

instance Ord a => Eval (AnalysisSetFamily a) where
  eval sf = uncurry MkStore <$> getSetFamily sf

instance Eval (AnalysisExpr r) where
  eval (SetFamily sf) = eval sf
  eval (BaseVal b) = constStore b
  eval (MonoidVal m) = evalSensExpr m
  eval (BoolVal b) = constStore b
  eval Empty = constStore mempty

  eval (Union xs ys) = evalBinary Set.union xs ys
  eval (UnionSingle xs x) = evalBinary Set.insert x xs
  eval (Pair x y) = evalBinary (,) x y
  eval (Fst p) = evalUnary fst p
  eval (Snd p) = evalUnary snd p
  eval (In x xs) = evalBinary Set.member x xs
  eval (And x y) = evalBinary (&&) x y
  eval (BaseEqual x y) = evalBinary (==) x y
  eval (MonoidEqual x y) = evalBinary (==) x y
  eval (Ite c t f) = evalBinary ifThenElse c t f

ifThenElse :: Bool -> a -> a -> a
ifThenElse True t _ = t
ifThenElse False _ f = f

class BuildVerifyInfo a where
  buildVerifyInfo :: a -> Verify s ()

instance BuildVerifyInfo (AnalysisConstraint a) where
  buildVerifyInfo (SetFamily lhs :=: SetFamily rhs) = do
    (lhsX, lhsCell) <- getSetFamily lhs
    (rhsX, rhsCell) <- getSetFamily rhs

    liftST $ sameAt2 lhsX rhsX lhsCell rhsCell

  buildVerifyInfo (SetFamily lhs :=: Union xs ys) = undefined

  buildVerifyInfo (_ :>: _) = error "buildVerifyInfo: (:<:)"

-- class GetVerifyInfoLens f where
--   getVerifyInfoLens :: f a -> VerifyInfoLens (Maybe a)

-- newtype LamVar = LamVar Int

-- instance GetVerifyInfoLens AnalysisSetFamily where
--   getVerifyInfoLens (C_Entry n) =
--     verifyInfoCEntry . lens ($ n) (\f x y -> x >> f y) -- TODO: Make sure this works

--   getVerifyInfoLens (C_Exit n) =
--     verifyInfoCExit . lens ($ n) (\f x y -> x >> f y)

--   getVerifyInfoLens (E_Family n) =
--     verifyInfoE . lens ($ n) (\f x y -> x >> f y)

--   getVerifyInfoLens (S_Family m n) =
--     verifyInfoS . lens ($ (m, n)) (\f x y -> x >> f y)

-- -- instance GetVerifyInfoLens SensExpr where
-- --   getVerifyInfoLens (SensAtom _) = error "getVerifyInfoLens: SensAtom"
-- --   getVerifyInfoLens (SensT n) =
-- --     verifyInfoT . lens ($ n) (\f x y -> x >> f y)

-- class BuildVerifyInfo a where
--   buildVerifyInfo :: a -> Verify ()

-- instance BuildVerifyInfo (AnalysisConstraint a) where
--   buildVerifyInfo (SetFamily x :=: SetFamily y) =
--     assignValue (getVerifyInfoLens x) (getVerifyInfoLens y)

