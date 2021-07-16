-- | Based on Tom Harding's propagators: https://www.youtube.com/watch?v=qYmW4TSBnVI
--

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TupleSections #-}

module Propagator where

import           Prelude hiding (id, (.))
import           Data.STRef
import           Control.Monad.ST
import           Control.Category
import           Control.Applicative
import           Control.Monad

import qualified Data.Map as Map
import           Data.Map (Map)

import           Data.Functor.Apply

import           Data.Maybe (catMaybes)

-- TODO: Keep track of the origin of inconsistencies
data Defined a
  = Unknown
  | Known a
  | Inconsistent
  deriving (Eq, Ord, Show, Read, Functor)

instance Apply Defined where
  (<.>) = (<*>)

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
newtype MapDefined a b = MkMapDefined (Defined (Map a b))
  deriving (Functor, Eq)
  -- deriving (Functor, Apply)

instance Ord a => Apply (MapDefined a) where
  MkMapDefined (Known f) <.> MkMapDefined (Known x) = MkMapDefined (Known (f <.> x))
  MkMapDefined Inconsistent <.> _ = MkMapDefined Inconsistent
  _ <.> MkMapDefined Inconsistent = MkMapDefined Inconsistent
  _ <.> _ = MkMapDefined Unknown

mapDefined :: Map a b -> MapDefined a b
mapDefined = MkMapDefined . Known

pointMap :: Ord a => (a, b) -> MapDefined a b
pointMap (x, y) = mapDefined $ Map.fromList [(x, y)]

pointRestriction :: Ord a => a -> MapDefined a b -> MapDefined a b
pointRestriction x (MkMapDefined (Known m)) =
  case Map.lookup x m of
    Nothing -> MkMapDefined Unknown
    Just y  -> pointMap (x, y)
pointRestriction _ md = md

mapDefinedLookup :: Ord a => MapDefined a b -> a -> Defined b
mapDefinedLookup (MkMapDefined (Known m)) x =
  case Map.lookup x m of
    Just r -> Known r
    Nothing -> Unknown
mapDefinedLookup (MkMapDefined Unknown) _ = Unknown
mapDefinedLookup (MkMapDefined Inconsistent) _ = Inconsistent

mapDefinedCompose :: forall a b c. (Ord a, Ord b) => MapDefined b c -> MapDefined a b -> MapDefined a c
mapDefinedCompose (MkMapDefined (Known f)) (MkMapDefined (Known g)) =
  let gAssocs = Map.assocs g
  in
  case map go gAssocs of
    [] -> MkMapDefined Unknown
    xs -> MkMapDefined $ Known $ Map.fromList $ catMaybes xs
  where
    go :: (a, b) -> Maybe (a, c)
    go (x, y) =
      case Map.lookup y f of
        Just z -> Just (x, z)
        Nothing -> Nothing

instance (Ord a, Eq b) => Semigroup (MapDefined a b) where
  MkMapDefined (Known m1) <> MkMapDefined (Known m2) =
    if or . Map.elems $ Map.intersectionWith (/=) m1 m2
      then MkMapDefined Inconsistent
      else MkMapDefined (Known (m1 <> m2))

  MkMapDefined x <> MkMapDefined y = MkMapDefined (x <> y)

instance (Ord a, Eq b) => Monoid (MapDefined a b) where
  mempty = MkMapDefined Unknown

mapDefinedImage :: Ord a => MapDefined a b -> [a] -> Defined [b]
mapDefinedImage md xs =
  sequenceA $ map (mapDefinedLookup md) xs

mapDefinedExtend :: (Ord a, Eq b) => MapDefined a b -> (a, b) -> MapDefined a b
mapDefinedExtend (MkMapDefined Unknown) p = pointMap p
mapDefinedExtend (MkMapDefined Inconsistent) _ = MkMapDefined Inconsistent
mapDefinedExtend md@(MkMapDefined (Known m)) (x, y) =
  case Map.lookup x m of
    Nothing -> MkMapDefined (Known (Map.insert x y m))
    Just y' ->
      if y' == y
        then md
        else MkMapDefined Inconsistent

newtype IxedCell s a b = MkIxedCell { getIxedCell :: STRef s (ST s (), MapDefined a b) }

ixedCell :: MapDefined a b -> ST s (IxedCell s a b)
ixedCell df = MkIxedCell <$> newSTRef (pure (), df)

-- known :: a -> ST s (IxedCell s x a)
-- known x = MkIxedCell <$> newSTRef (definedFun (const (Known x)))

knownAt :: Ord x => (x, a) -> ST s (IxedCell s x a)
knownAt p = MkIxedCell <$> newSTRef (pure (), pointMap p)

unknown :: ST s (IxedCell s x a)
unknown = MkIxedCell <$> newSTRef (pure (), MkMapDefined Unknown)

readIxedCell :: IxedCell s x a -> ST s (MapDefined x a)
readIxedCell (MkIxedCell ref) =
  snd <$> readSTRef ref

-- TODO: Propagate inconsistencies here?
readIxedCellAt :: Ord x => IxedCell s x a -> x -> ST s (Defined a)
readIxedCellAt (MkIxedCell ref) x =
  (`mapDefinedLookup` x) . snd <$> readSTRef ref

ixedCellImage :: Ord x => IxedCell s x a -> [x] -> ST s (Defined [a])
ixedCellImage c xs =
  fmap sequenceA $ mapM (readIxedCellAt c) xs

updateDefined :: (Ord x, Eq a) => IxedCell s x a -> MapDefined x a -> ST s ()
updateDefined (MkIxedCell c) x = do
  (act, md) <- readSTRef c
  let mdx = md <> x
  writeSTRef c (act, mdx)
  when (mdx /= md) act
  -- where
  --   go (def, act) = (def <> x, act)

-- -- -- -- updateDefinedAct :: Eq a => IxedCell s x a -> DefinedFun x a -> ST s () -> ST s ()
-- -- -- -- updateDefinedAct c@(MkIxedCell ref) x act = do
-- -- -- --   updateDefined c x
-- -- -- --   modifySTRef ref (\(def, origAct) -> (def, origAct *> act))

getAct :: IxedCell s x a -> ST s ()
getAct (MkIxedCell c) = fst =<< readSTRef c

-- TODO: Propagate inconsistencies here?
update :: (Ord x, Eq a) => IxedCell s x a -> (x, a) -> ST s ()
update c@(MkIxedCell ref) (x, y) = do
  -- md <- readIxedCellAt c x
  (act, md) <- readSTRef ref
  writeSTRef ref (act, mapDefinedExtend md (x, y))
  act
  -- act
  -- updateDefined c (definedFun f)
  -- where
  --   f z
  --     | z == x    = Known y
  --     | otherwise = Unknown

watch :: IxedCell s x a -> (MapDefined x a -> ST s ()) -> ST s ()
watch c@(MkIxedCell ref) k = do
  (act, md) <- readSTRef ref
  writeSTRef ref (act *> prop md, md)
  -- modifySTRef ref (`extendAct` prop)
  prop md
  where
    prop md = do -- k md
      (act, md) <- readSTRef ref
      k md
    -- go def = (def, act *> prop)

unary :: (Ord x, Eq a, Eq b) => (a -> b) -> IxedCell s x a -> IxedCell s x b -> ST s ()
unary f cX cY =
  watch cX (updateDefined cY . fmap f)
  -- watch cX (updateDefined cY . (knownFun f .))

unaryAt :: (Ord x, Eq a, Eq b) => x -> (a -> b) -> IxedCell s x a -> IxedCell s x b -> ST s ()
unaryAt x f c1 c2 =
  watch c1 (updateDefined c2 . fmap f . pointRestriction x)

binary :: forall s x a b c. (Ord x, Eq a, Eq b, Eq c) => (a -> b -> c) -> IxedCell s x a -> IxedCell s x b -> IxedCell s x c -> ST s ()
binary f cA cB cC = do
  watch cA $ \g -> do
    readIxedCell cB >>= \h ->
      updateDefined cC (go g h) --liftA2 f <$> applyDefinedFun g <*> applyDefinedFun h))

  watch cB $ \g -> do
    readIxedCell cA >>= \h ->
      updateDefined cC (go h g)
  where
    go :: MapDefined x a -> MapDefined x b -> MapDefined x c
    go g h = f <$> g <.> h

type Cell s = IxedCell s ()

known :: a -> ST s (Cell s a)
known x = knownAt ((), x)

readCell :: Cell s a -> ST s (Defined a)
readCell c = readIxedCellAt c ()

sameAt :: (Ord x, Eq a) => x -> IxedCell s x a -> IxedCell s x a -> ST s ()
sameAt x c1 c2 = do
  unaryAt x id c1 c2
  unaryAt x id c2 c1

-- sameAt :: x -> IxedCell s x a -> IxedCell s x a -> ST s ()
-- sameAt x c1 c2 = do
--   unary go c1 c2
--   unary go c2 c1
--   where
--     go x' =
--       if x' == x
--         then 



add :: (Ord x, Eq a, Num a) => IxedCell s x a -> IxedCell s x a -> IxedCell s x a -> ST s ()
add cX cY cZ = do
    -- cX + cY = cZ
  binary (+) cX cY cZ

    -- cZ - cY = cX
  binary (-) cZ cY cX

    -- cZ - cX = cY
  binary (-) cZ cX cY

negation :: (Ord x, Eq a, Num a) => IxedCell s x a -> IxedCell s x a -> ST s ()
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

  sameAt () x y


  [a, b, c] <- mapM readCell [z, w, o]
  return (a, b, c)

-- -- {-
-- -- example2 :: forall s. ST s (Defined Int)
-- -- example2 = do
-- --   x <- ixedCell (pointFun ('a', 1))
-- --   y <- ixedCell (pointFun ('a', 2))
-- --   z <- unknown
-- --   w <- unknown

-- --   joinIxedCellsAt 'b' x w

-- --   updateDefined x $ pointFun ('b', 1)

-- --   add x y z
-- --   readIxedCellAt w 'a'
-- -- -}

