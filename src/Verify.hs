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

import qualified Data.ByteString as BS

import           Data.Maybe (maybeToList)

import qualified Data.List as L
import qualified Data.Set as Set

import           Data.Set (Set)

-- import           Lens.Micro
-- import           Lens.Micro.TH

import           Control.Monad.ST
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
    , verifyInfoT :: IxedCell s NodeId Sensitivity
    , verifyInfoS :: IxedCell s (NodeId, NodeId) (Set (Var, SensExpr))
    }

getSetFamily :: VerifyInfo s -> AnalysisSetFamily a b -> (a, IxedCell s a b)
getSetFamily vi (C_Entry n) = (n, verifyInfoCEntry vi)
getSetFamily vi (C_Exit  n) = (n, verifyInfoCExit  vi)
getSetFamily vi (S_Family m n) = ((m, n), verifyInfoS vi)
getSetFamily vi (E_Family n) = (n, verifyInfoE vi)
getSetFamily vi (B_Family {}) = error "getSetFamily: B_Family"


-- | c1(x) U c2(x) = rhs
unionAt :: (Ord a, Ord b) => a -> IxedCell s a (Set b) -> IxedCell s a (Set b) -> IxedCell s a (Set b) -> ST s ()
unionAt x c1 c2 rhs = do
  binaryAt x Set.union c1 c2 rhs
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

class BuildVerifyInfo a where
  buildVerifyInfo :: a -> Verify s ()

instance BuildVerifyInfo (AnalysisConstraint a) where
  buildVerifyInfo (SetFamily x :=: SetFamily y) = undefined
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

