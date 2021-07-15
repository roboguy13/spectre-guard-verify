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

data ActionDefined s a
  = CanAct (ST s ()) (Defined a)
  | DoneActing (Defined a)
  deriving (Functor)

-- TODO: Should this take actions into account?
instance Applicative (ActionDefined s) where
  pure = CanAct (pure ()) . pure
  DoneActing f <*> DoneActing x = DoneActing (f <*> x)
  CanAct actF f <*> CanAct actX x = CanAct (actF *> actX) (f <*> x)
  CanAct actF f <*> DoneActing x = CanAct actF (f <*> x)
  DoneActing f <*> CanAct actX x = CanAct actX (f <*> x)

getDefined :: ActionDefined s a -> Defined a
getDefined (CanAct _ def) = def
getDefined (DoneActing def) = def

instance Eq a => Semigroup (ActionDefined s a) where
  DoneActing x <> DoneActing y = DoneActing (x <> y)
  CanAct actX x <> DoneActing y = CanAct actX (x <> y)
  DoneActing x <> CanAct actY y = CanAct actY (x <> y)
  CanAct actX x <> CanAct actY y = CanAct (actX *> actY) (x <> y)

instance Eq a => Monoid (ActionDefined s a) where
  mempty = CanAct (pure ()) mempty

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
newtype DefinedFun s a b = MkDefinedFun { runDefinedFun :: a -> ActionDefined s b }

actDefinedFun :: Eq a => DefinedFun s a b -> a -> ST s (Defined b, DefinedFun s a b)
actDefinedFun defFun@(MkDefinedFun f) x =
  let fx = f x
  in
  case fx of
    CanAct act def@(Known _) -> do -- TODO: Should this just trigger on 'Known'?
      act
      pure (def, modified def)

    CanAct act def -> act *> pure (def, defFun)

    DoneActing def -> pure (def, defFun)
  where
    modified def = MkDefinedFun $ \x' ->
      if x' == x
        then DoneActing def
        else f x'

instance Eq b => Semigroup (DefinedFun s a b) where
  MkDefinedFun f <> MkDefinedFun g =
    MkDefinedFun (f <> g)

instance Eq b => Monoid (DefinedFun s a b) where
  mempty = constDefinedFun Unknown

instance Category (DefinedFun s) where
  id = knownFun id
  MkDefinedFun f . MkDefinedFun g = MkDefinedFun $ \x ->
    case g x of
      CanAct act def -> extendAct (go def) act
    where
      go (Known x')   = f x'
      go Unknown      = CanAct (pure ()) Unknown
      go Inconsistent = CanAct (pure ()) Inconsistent

definedFun :: (a -> Defined b) -> DefinedFun s a b
definedFun f = MkDefinedFun (CanAct (pure ()) . f)

knownFun :: (a -> b) -> DefinedFun s a b
knownFun f = definedFun (Known . f)

pointFun :: Eq a => (a, b) -> DefinedFun s a b
pointFun (x, y) = definedFun $ \z ->
  if z == x
    then Known y
    else Unknown

extendAct :: ActionDefined s a -> ST s () -> ActionDefined s a
extendAct (CanAct act x) act2 = CanAct (act *> act2) x
extendAct (DoneActing x) act = CanAct act x -- TODO: Should this be like that?

extendFunAct :: DefinedFun s a b -> ST s () -> DefinedFun s a b
extendFunAct defFun newAct = MkDefinedFun go
  where
    go x =
      case runDefinedFun defFun x of
        CanAct act y -> CanAct (act *> newAct) y
        -- DoneActing y -> CanAct newAct y -- TODO: Should this be like that
        DoneActing y -> DoneActing y

constDefinedFun :: Defined b -> DefinedFun s a b
constDefinedFun = definedFun . const

inconsistentDefinedFun :: DefinedFun s a b
inconsistentDefinedFun = constDefinedFun Inconsistent

-- -- | Nothing = <inconsistent>
-- extendDefinedFun' :: (Eq a, Eq b) => DefinedFun s a b -> (a, b) -> Maybe (DefinedFun s a b)
-- extendDefinedFun' df@(MkDefinedFun f) (x, y) =
--   case f x of
--     Unknown -> Just (pointFun (x, y) <> df)
--     -- Unknown -> Just . MkDefinedFun $ \z ->
--     --   if z == x
--     --     then Known y
--     --     else f z
--     Known y'
--       | y' == y -> Just df
--     _ -> Nothing

-- extendDefinedFun :: (Eq a, Eq b) => DefinedFun a b -> (a, b) -> DefinedFun a b
-- extendDefinedFun df p =
--   case extendDefinedFun' df p of
--     Just df' -> df
--     Nothing -> inconsistentDefinedFun

definedFunImage :: DefinedFun s a b -> [a] -> Defined [b]
definedFunImage (MkDefinedFun f) = sequenceA . map (getDefined . f)

newtype IxedCell s a b = MkIxedCell { getIxedCell :: STRef s (DefinedFun s a b) }

ixedCell :: DefinedFun s a b -> ST s (IxedCell s a b)
ixedCell df = MkIxedCell <$> newSTRef df

known :: a -> ST s (IxedCell s x a)
known x = MkIxedCell <$> newSTRef (constDefinedFun (Known x))

unknown :: ST s (IxedCell s x a)
unknown = MkIxedCell <$> newSTRef (constDefinedFun Unknown)

readIxedCell :: IxedCell s x a -> ST s (DefinedFun s x a)
readIxedCell (MkIxedCell ref) =
  readSTRef ref

-- TODO: Propagate inconsistencies here?
readIxedCellAt :: IxedCell s x a -> x -> ST s (Defined a)
readIxedCellAt (MkIxedCell ref) x = do
  fmap (`runDefinedFun` x) (readSTRef ref) >>= \case
    CanAct act def -> act *> pure def
    DoneActing def -> pure def

-- readIxedCellAt c x = getDefined . (`runDefinedFun` x) <$> readIxedCell c

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

-- -- updateDefinedAct :: Eq a => IxedCell s x a -> DefinedFun x a -> ST s () -> ST s ()
-- -- updateDefinedAct c@(MkIxedCell ref) x act = do
-- --   updateDefined c x
-- --   modifySTRef ref (\(def, origAct) -> (def, origAct *> act))

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
  modifySTRef ref (`extendFunAct` prop)
  -- prop
  where
    prop = do
      fun <- readSTRef ref
      k fun
    -- go def = (def, act *> prop)

unary :: (Eq a, Eq b) => (a -> b) -> IxedCell s x a -> IxedCell s x b -> ST s ()
unary f cX cY =
  watch cX (updateDefined cY . (knownFun f .))

-- unaryCtx :: forall s x a b. (Eq a, Eq b) => ((x, a) -> Defined b) -> ((x, b) -> Defined a) -> IxedCell s x a -> IxedCell s x b -> ST s ()
-- unaryCtx f g cX cY@(MkIxedCell cY_ref) = do
--   -- (cY_fun, _) <- readSTRef cY_ref
--   watch cX (updateDefined cY . MkDefinedFun . go f)
--   watch cY (updateDefined cX . MkDefinedFun . go g)
--   where
--     -- go :: DefinedFun x a -> x -> Defined b
--     go fun d x =
--       case runDefinedFun d x of
--         Inconsistent -> Inconsistent
--         Unknown -> Unknown
--         Known dx -> fun (x, dx)
--           -- case f (x, dx) of
--           --   Inconsistent -> Inconsistent
--           --   Known r -> Known r
--           --   Unknown -> runDefinedFun cY_fun x

binary :: (Eq a, Eq b, Eq c) => (a -> b -> c) -> IxedCell s x a -> IxedCell s x b -> IxedCell s x c -> ST s ()
binary f cA cB cC = do
  watch cA $ \g -> do
    readIxedCell cB >>= \h ->
      updateDefined cC (MkDefinedFun (liftA2 f <$> runDefinedFun g <*> runDefinedFun h))

  watch cB $ \g -> do
    readIxedCell cA >>= \h ->
      updateDefined cC (MkDefinedFun (liftA2 f <$> runDefinedFun h <*> runDefinedFun g))

-- joinIxedCellsAt :: forall s x a. (Eq x, Eq a) => x -> IxedCell s x a -> IxedCell s x a -> ST s ()
-- joinIxedCellsAt x c1 c2 = unaryCtx go go c1 c2
--   where
--     -- go :: (x, a) -> Defined a
--     go (x', r) =
--       if x' == x
--         then Known r
--         else Unknown --liftA2 (<>) (readIxedCellAt c1 x') (readIxedCellAt c2 x')

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

{-
example2 :: forall s. ST s (Defined Int)
example2 = do
  x <- ixedCell (pointFun ('a', 1))
  y <- ixedCell (pointFun ('a', 2))
  z <- unknown
  w <- unknown

  joinIxedCellsAt 'b' x w

  updateDefined x $ pointFun ('b', 1)

  add x y z
  readIxedCellAt w 'a'
-}

