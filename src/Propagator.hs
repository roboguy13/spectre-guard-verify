-- | Based on Tom Harding's propagators: https://www.youtube.com/watch?v=qYmW4TSBnVI
--

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}

module Propagator where

import           Prelude hiding (id, (.))
import           Data.STRef
import           Control.Monad.ST
import           Control.Category
import           Control.Applicative

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
  _ <> _            = Unknown

instance Eq a => Monoid (Defined a) where
  mempty = Unknown

instance Applicative Defined where
  pure = Known
  Known f <*> Known x = Known (f x)
  Inconsistent <*> _ = Inconsistent
  _ <*> Inconsistent = Inconsistent
  Unknown <*> _ = Unknown
  _ <*> Unknown = Unknown

-- -- NOTE: 'ap' is different from (<*>) with this:
-- instance Monad Defined where
--   return = pure
--   Inconsistent >>= _ = Inconsistent
--   x >>= f = theJoin (fmap f x)
--     where
--       theJoin (Known (Known k)) = Known k
--       theJoin Unknown = Unknown
--       theJoin Inconsistent = Inconsistent

applyToDefined :: (a -> b) -> Defined a -> Defined b
applyToDefined = fmap

applyToDefined2 :: (a -> b -> c) -> Defined a -> Defined b -> Defined c
applyToDefined2 = liftA2

-- | Indexed (partial function-like) version of @Defined@
newtype DefinedFun a b = MkDefinedFun { runDefinedFun :: a -> Defined b }

instance Eq b => Semigroup (DefinedFun a b) where
  MkDefinedFun f <> MkDefinedFun g =
    MkDefinedFun (f <> g)

instance Eq b => Monoid (DefinedFun a b) where
  mempty = constDefinedFun Unknown

instance Category DefinedFun where
  id = definedFun id
  MkDefinedFun f . MkDefinedFun g = MkDefinedFun $ \x ->
    case g x of
      Known x' -> f x'
      Unknown -> Unknown
      Inconsistent -> Inconsistent

definedFun :: (a -> b) -> DefinedFun a b
definedFun f = MkDefinedFun (Known . f)

pointFun :: Eq a => (a, b) -> DefinedFun a b
pointFun (x, y) = MkDefinedFun $ \z ->
  if z == x
    then Known y
    else Unknown

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
    Unknown -> Just (pointFun (x, y) <> df)
    -- Unknown -> Just . MkDefinedFun $ \z ->
    --   if z == x
    --     then Known y
    --     else f z
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

newtype IxedCell s a b = MkIxedCell { getIxedCell :: STRef s (DefinedFun a b, ST s ()) }

ixedCell :: DefinedFun a b -> ST s (IxedCell s a b)
ixedCell df = MkIxedCell <$> newSTRef (df, pure ())

known :: a -> ST s (IxedCell s x a)
known x = MkIxedCell <$> newSTRef (constDefinedFun (Known x), pure ())

unknown :: ST s (IxedCell s x a)
unknown = MkIxedCell <$> newSTRef (constDefinedFun Unknown, pure ())

readIxedCell :: IxedCell s x a -> ST s (DefinedFun x a)
readIxedCell (MkIxedCell ref) = do
  (x, _) <- readSTRef ref
  return x

-- TODO: Propagate inconsistencies here?
readIxedCellAt :: IxedCell s x a -> x -> ST s (Defined a)
readIxedCellAt c x = (`runDefinedFun` x) <$> readIxedCell c

ixedCellImage :: IxedCell s x a -> [x] -> ST s (Defined [a])
ixedCellImage c xs = fmap sequenceA (mapM (flip runDefinedFun) xs <$> readIxedCell c)

updateDefined :: Eq a => IxedCell s x a -> DefinedFun x a -> ST s ()
updateDefined (MkIxedCell c) x = do
    (_, act) <- readSTRef c
    modifySTRef c go
    -- act
  where
    go (def, act) = (def <> x, act)

-- TODO: Propagate inconsistencies here?
update :: (Eq x, Eq a) => IxedCell s x a -> (x, a) -> ST s ()
update c (x, y) = do
  r <- readIxedCellAt c x
  updateDefined c (MkDefinedFun f)
  where
    f z
      | z == x    = Known y
      | otherwise = Unknown

watch :: IxedCell s x a -> (DefinedFun x a -> ST s ()) -> ST s ()
watch c@(MkIxedCell ref) k = do
  modifySTRef ref go
  (_, act) <- readSTRef ref
  act
  where
    prop = do
      (fun, act) <- readSTRef ref
      k fun
    go (def, act) = (def, act *> prop)

unary :: (Eq a, Eq b) => (a -> b) -> IxedCell s x a -> IxedCell s x b -> ST s ()
unary f cX cY = do
  watch cX (updateDefined cY . (definedFun f .))

binary :: (Eq a, Eq b, Eq c) => (a -> b -> c) -> IxedCell s x a -> IxedCell s x b -> IxedCell s x c -> ST s ()
binary f cA cB cC = do
  watch cA $ \g -> do
    readIxedCell cB >>= \h ->
      updateDefined cC (MkDefinedFun (liftA2 f <$> runDefinedFun g <*> runDefinedFun h))

  watch cB $ \g -> do
    readIxedCell cA >>= \h ->
      updateDefined cC (MkDefinedFun (liftA2 f <$> runDefinedFun h <*> runDefinedFun g))

type Cell s = IxedCell s ()

readCell :: Cell s a -> ST s (Defined a)
readCell c = readIxedCellAt c ()

add :: (Eq a, Num a) => IxedCell s x a -> IxedCell s x a -> IxedCell s x a -> ST s ()
add cX cY cZ = do
    -- cX + cY = cZ
  binary (+) cX cY cZ

    -- cZ - cY = cX
  binary (-) cZ cY cX

    -- cZ - cX = cY
  binary (-) cZ cX cY

negation :: (Eq a, Num a) => IxedCell s x a -> IxedCell s x a -> ST s ()
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

example2 :: forall s. ST s (Defined Int)
example2 = do
  x <- ixedCell (pointFun ('a', 1))
  y <- ixedCell (pointFun ('a', 2))
  z <- unknown

  updateDefined x $ pointFun ('a', 10)

  add x y z
  readIxedCellAt x 'a'

