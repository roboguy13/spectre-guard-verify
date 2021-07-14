-- | Based on Tom Harding's propagators: https://www.youtube.com/watch?v=qYmW4TSBnVI
--

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}

module Propagator where

import           Data.STRef
import           Control.Monad.ST

-- TODO: Keep track of the origin of inconsistencies
data Defined a
  = Unknown
  | Known a
  | Inconsistent
  deriving (Eq, Ord, Show, Read, Functor)


instance Eq a => Semigroup (Defined a) where
  Inconsistent <> _ = Inconsistent
  _ <> Inconsistent = Inconsistent
  Known x <> Known y
    | x == y        = Known x
    | otherwise     = Inconsistent
  Known x <> _      = Known x
  _ <> Known y      = Known y

instance Eq a => Monoid (Defined a) where
  mempty = Unknown

instance Applicative Defined where
  pure = Known
  Known f <*> Known x = Known (f x)
  Inconsistent <*> _ = Inconsistent
  _ <*> Inconsistent = Inconsistent
  Unknown <*> _ = Unknown
  _ <*> Unknown = Unknown

-- | Indexed (partial function-like) version of @Defined@
newtype DefinedFun a b = MkDefinedFun { runDefinedFun :: a -> Defined b }

instance Eq b => Semigroup (DefinedFun a b) where
  MkDefinedFun f <> MkDefinedFun g =
    MkDefinedFun (f <> g)

fromUnitDefinedFun :: DefinedFun () a -> Defined a
fromUnitDefinedFun (MkDefinedFun f) = f ()

toUnitDefinedFun :: Defined a -> DefinedFun () a
toUnitDefinedFun = constDefinedFun

constDefinedFun :: Defined b -> DefinedFun a b
constDefinedFun = MkDefinedFun . const

inconsistentDefinedFun :: DefinedFun a b
inconsistentDefinedFun = constDefinedFun Inconsistent

-- | Nothing = <inconsistent>
extendDefinedFun' :: (Eq a, Eq b) => DefinedFun a b -> (a, b) -> Maybe (DefinedFun a b)
extendDefinedFun' df@(MkDefinedFun f) (x, y) =
  case f x of
    Unknown -> Just . MkDefinedFun $ \z ->
      if z == x
        then Known y
        else f z
    Known y'
      | y' == y -> Just df
    _ -> Nothing

extendDefinedFun :: (Eq a, Eq b) => DefinedFun a b -> (a, b) -> DefinedFun a b
extendDefinedFun df p =
  case extendDefinedFun' df p of
    Just df' -> df
    Nothing -> inconsistentDefinedFun

definedFunImage :: DefinedFun a b -> [a] -> Defined [b]
definedFunImage (MkDefinedFun f) = sequenceA . map f

newtype Cell s a = MkCell { getCell :: STRef s (Defined a, ST s ()) }

known :: a -> ST s (Cell s a)
known x = MkCell <$> newSTRef (Known x, pure ())

unknown :: ST s (Cell s a)
unknown = MkCell <$> newSTRef (Unknown, pure ())

readCell :: Cell s a -> ST s (Defined a)
readCell (MkCell ref) = do
  (x, _) <- readSTRef ref
  return x

updateDefined :: Eq a => Cell s a -> Defined a -> ST s ()
updateDefined (MkCell c) x = do
    (_, act) <- readSTRef c
    modifySTRef c go
    -- act
  where
    go (def, act) = (def <> x, act)

update :: Eq a => Cell s a -> a -> ST s ()
update c = updateDefined c . Known

watch :: Cell s a -> (a -> ST s ()) -> ST s ()
watch c@(MkCell ref) k = do
  modifySTRef ref go
  (_, act) <- readSTRef ref
  act
  where
    prop = do
      (def, act) <- readSTRef ref
      case def of
        Known x -> k x
        _ -> pure ()
    go (def, act) = (def, act *> prop)

-- link :: Eq a => Cell s a -> Cell s a -> ST s ()
-- link xC@(MkCell x) yC@(MkCell y) = do
--   (xVal, actX) <- readSTRef x
--   (yVal, actY) <- readSTRef y
--   modifySTRef x (go yC yVal actY)
--   actX
--   modifySTRef y (go xC xVal actX)
--   actY
--   where
--     go c val otherAct (def, act) =
--       (def <> val, otherAct <> updateDefined c def <> act)

unary :: (Eq a, Eq b) => (a -> b) -> Cell s a -> Cell s b -> ST s ()
unary f cX cY = do
  watch cX (update cY . f)

binary :: (Eq a, Eq b, Eq c) => (a -> b -> c) -> Cell s a -> Cell s b -> Cell s c -> ST s ()
binary f cX cY cZ = do
  watch cX $ \x -> do
    readCell cY >>= \case
      Known y -> update cZ (f x y)
      _ -> pure ()

  watch cY $ \y -> do
    readCell cX >>= \case
      Known x -> update cZ (f x y)
      _ -> pure ()

add :: (Eq a, Num a) => Cell s a -> Cell s a -> Cell s a -> ST s ()
add cX cY cZ = do
    -- cX + cY = cZ
  binary (+) cX cY cZ

    -- cZ - cY = cX
  binary (-) cZ cY cX

    -- cZ - cX = cY
  binary (-) cZ cX cY

negation :: (Eq a, Num a) => Cell s a -> Cell s a -> ST s ()
negation cX cY = do
  unary negate cX cY
  unary negate cY cX




example1 :: forall s. ST s (Defined Int, Defined Int, Defined Int)
example1 = do
  x <- known 2 :: ST s (Cell s Int)
  y <- known 3 :: ST s (Cell s Int)

  z <- unknown
  w <- unknown
  o <- unknown

  add x y z
  negation z w
  add y w o

  [a, b, c] <- mapM readCell [z, w, o]
  return (a, b, c)

