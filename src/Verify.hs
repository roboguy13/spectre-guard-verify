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

-- makeLenses ''VerifyInfo

-- type VerifyInfoLens s a = Lens' (VerifyInfo s) a

-- extendValue' :: Eq a => (a -> Maybe b) -> (a, b) -> Maybe (a -> Maybe b)
-- extendValue' f (x, s) =
--   case f x of
--     Just _ -> Nothing -- Inconsistency
--     Nothing -> Just $ \y ->
--       if y == x
--         then Just s
--         else f y

-- extendValue :: VerifyInfoLens (Holmes b) -> Holmes b -> Verify ()
-- extendValue lens p = do
--   undefined unify


  -- value_maybe <- fmap (^. lens) get
  -- case value_maybe of
  --   Nothing -> inconsistent "!"
  --   Just value' -> modify (lens .~ Just value')

-- assignValue :: VerifyInfoLens (Maybe b) -> VerifyInfoLens (Maybe b) -> Verify ()
-- assignValue targetLens lens = do
--   x <- fmap (^. lens) get
--   modify (targetLens .~ x)



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

