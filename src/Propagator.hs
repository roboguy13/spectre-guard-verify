-- | Based on Tom Harding's propagators: https://www.youtube.com/watch?v=qYmW4TSBnVI
--

{-# LANGUAGE DeriveFunctor #-}
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
newtype DefinedFun s a b = MkDefinedFun (ST s (), a -> Defined b)

definedFun :: (a -> Defined b) -> DefinedFun s a b
definedFun f = do
  MkDefinedFun (pure (), f)

knownFun :: (a -> b) -> DefinedFun s a b
knownFun f = definedFun (Known . f)

pointFun :: Eq a => (a, b) -> DefinedFun s a b
pointFun (x, y) = definedFun $ \z ->
  if z == x
    then Known y
    else Unknown

inconsistentFun :: DefinedFun s a b
inconsistentFun = definedFun (const Inconsistent)

setDefinedFun :: (Eq a, Eq b) => (a, b) -> DefinedFun s a b -> ST s (DefinedFun s a b)
setDefinedFun (x, y) df@(MkDefinedFun (act, f)) =
  case f x of
    Known y' ->
      if y' == y
        then act *> pure df
        else pure inconsistentFun
    Unknown -> act *> pure go
    Inconsistent -> pure inconsistentFun
  where
    go = MkDefinedFun $ \z ->
      if z == x
        then (Known y, pure ())
        else f z

applyDefinedFun :: DefinedFun s a b -> a -> ST s (Defined b)
applyDefinedFun (MkDefinedFun f) x =
  let (def, act) = f x
  in
  act *> pure def

extendAct :: DefinedFun s a b -> ST s () -> DefinedFun s a b
extendAct (MkDefinedFun f) newAct = MkDefinedFun $ \z ->
  let (def, act) = f z
  in
  (def, act *> newAct)

instance Eq b => Semigroup (DefinedFun s a b) where
  MkDefinedFun f <> MkDefinedFun g =
    MkDefinedFun (f <> g)

instance Eq b => Monoid (DefinedFun s a b) where
  mempty = definedFun (const Unknown)

instance Category (DefinedFun s) where
  id = knownFun id
  MkDefinedFun f . MkDefinedFun g = MkDefinedFun $ \x ->
    let (gDef, gAct) = g x
    in
    case f <$> gDef of
      Unknown -> (Unknown, gAct)
      Inconsistent -> (Inconsistent, gAct) -- TODO: Should this be pure ()?
      Known z -> go gAct z

    where
      go gAct (Known x', act) = (Known x', gAct *> act)
      go gAct (Unknown, act) = (Unknown, gAct *> act)
      go gAct (Inconsistent, act) = (Inconsistent, gAct *> act) -- TODO: Should this be pure ()?

definedFunImage :: DefinedFun s a b -> [a] -> Defined [b]
definedFunImage (MkDefinedFun f) = sequenceA . map (fst . f)

newtype IxedCell s a b = MkIxedCell { getIxedCell :: STRef s (DefinedFun s a b) }

ixedCell :: DefinedFun s a b -> ST s (IxedCell s a b)
ixedCell df = MkIxedCell <$> newSTRef df

known :: a -> ST s (IxedCell s x a)
known x = MkIxedCell <$> newSTRef (definedFun (const (Known x)))

unknown :: ST s (IxedCell s x a)
unknown = MkIxedCell <$> newSTRef (definedFun (const Unknown))

readIxedCell :: IxedCell s x a -> ST s (DefinedFun s x a)
readIxedCell (MkIxedCell ref) =
  readSTRef ref

-- TODO: Propagate inconsistencies here?
readIxedCellAt :: IxedCell s x a -> x -> ST s (Defined a)
readIxedCellAt (MkIxedCell ref) x = do
  (`applyDefinedFun` x) =<< readSTRef ref

ixedCellImage :: IxedCell s x a -> [x] -> ST s (Defined [a])
ixedCellImage c xs = --fmap sequenceA (mapM ((getDefined .) . flip runDefinedFun) xs <$> readIxedCell c)
  fmap sequenceA $ mapM (readIxedCellAt c) xs

updateDefined :: Eq a => IxedCell s x a -> DefinedFun s x a -> ST s ()
updateDefined (MkIxedCell c) x = do
  defFun <- readSTRef c
  writeSTRef c (defFun <> x)
    -- act
  -- where
  --   go (def, act) = (def <> x, act)

-- -- -- updateDefinedAct :: Eq a => IxedCell s x a -> DefinedFun x a -> ST s () -> ST s ()
-- -- -- updateDefinedAct c@(MkIxedCell ref) x act = do
-- -- --   updateDefined c x
-- -- --   modifySTRef ref (\(def, origAct) -> (def, origAct *> act))

-- TODO: Propagate inconsistencies here?
update :: (Eq x, Eq a) => IxedCell s x a -> (x, a) -> ST s ()
update c (x, y) = do
  r <- readIxedCellAt c x

  updateDefined c (definedFun f)
  where
    f z
      | z == x    = Known y
      | otherwise = Unknown

watch :: IxedCell s x a -> (DefinedFun s x a -> ST s ()) -> ST s ()
watch c@(MkIxedCell ref) k = do
  modifySTRef ref (`extendAct` prop)
  -- prop
  where
    prop = do
      fun <- readSTRef ref
      k fun
    -- go def = (def, act *> prop)

unary :: (Eq a, Eq b) => (a -> b) -> IxedCell s x a -> IxedCell s x b -> ST s ()
unary f cX cY =
  watch cX (updateDefined cY . (knownFun f .))

-- -- unaryCtx :: forall s x a b. (Eq a, Eq b) => ((x, a) -> Defined b) -> ((x, b) -> Defined a) -> IxedCell s x a -> IxedCell s x b -> ST s ()
-- -- unaryCtx f g cX cY@(MkIxedCell cY_ref) = do
-- --   -- (cY_fun, _) <- readSTRef cY_ref
-- --   watch cX (updateDefined cY . MkDefinedFun . go f)
-- --   watch cY (updateDefined cX . MkDefinedFun . go g)
-- --   where
-- --     -- go :: DefinedFun x a -> x -> Defined b
-- --     go fun d x =
-- --       case runDefinedFun d x of
-- --         Inconsistent -> Inconsistent
-- --         Unknown -> Unknown
-- --         Known dx -> fun (x, dx)
-- --           -- case f (x, dx) of
-- --           --   Inconsistent -> Inconsistent
-- --           --   Known r -> Known r
-- --           --   Unknown -> runDefinedFun cY_fun x

binary :: forall s x a b c. (Eq a, Eq b, Eq c) => (a -> b -> c) -> IxedCell s x a -> IxedCell s x b -> IxedCell s x c -> ST s ()
binary f cA cB cC = do
  watch cA $ \g -> do
    readIxedCell cB >>= \h ->
      updateDefined cC (MkDefinedFun (go g h)) --liftA2 f <$> applyDefinedFun g <*> applyDefinedFun h))

  watch cB $ \g -> do
    readIxedCell cA >>= \h ->
      updateDefined cC (MkDefinedFun (go h g))
  where
    go :: DefinedFun s x a -> DefinedFun s x b -> x -> (Defined c, ST s ())
    go (MkDefinedFun g) (MkDefinedFun h) x =
      let (gDef, gAct) = g x
          (hDef, hAct) = h x
      in (f <$> gDef <*> hDef, gAct *> hAct)

-- -- joinIxedCellsAt :: forall s x a. (Eq x, Eq a) => x -> IxedCell s x a -> IxedCell s x a -> ST s ()
-- -- joinIxedCellsAt x c1 c2 = unaryCtx go go c1 c2
-- --   where
-- --     -- go :: (x, a) -> Defined a
-- --     go (x', r) =
-- --       if x' == x
-- --         then Known r
-- --         else Unknown --liftA2 (<>) (readIxedCellAt c1 x') (readIxedCellAt c2 x')

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

-- {-
-- example2 :: forall s. ST s (Defined Int)
-- example2 = do
--   x <- ixedCell (pointFun ('a', 1))
--   y <- ixedCell (pointFun ('a', 2))
--   z <- unknown
--   w <- unknown

--   joinIxedCellsAt 'b' x w

--   updateDefined x $ pointFun ('b', 1)

--   add x y z
--   readIxedCellAt w 'a'
-- -}

