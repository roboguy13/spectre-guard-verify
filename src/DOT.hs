{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE ScopedTypeVariables #-}

module DOT (genDOT, genDOT', DOTConfig(..), defaultDOTConfig) where

import           SetExpr
import           ConstraintGen

import           Data.Foldable
import           Data.Set (Set)
import qualified Data.Set as Set

import           Data.List

-- import           Data.Equivalence.Monad
import           Data.Equivalence.STT --(Equiv, leastEquiv)
import           Data.Functor.Identity
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Control.Monad.ST.Trans

type DOTEquiv s = Equiv s [NodeId] NodeId

newtype DOTM s a = DOTM { unDOTM :: ReaderT (DOTEquiv s, DOTEquiv s) (STT s Identity) a }
  deriving (Functor, Applicative, Monad, MonadReader (DOTEquiv s, DOTEquiv s))

entryEquiv :: DOTM s (DOTEquiv s)
entryEquiv = fst <$> ask

exitEquiv :: DOTM s (DOTEquiv s)
exitEquiv = snd <$> ask

-- onEntryEquiv :: (DOTEquiv s -> r) -> DOTM s r
-- onEntryEquiv f =
--   fmap f entryEquiv

liftSTT :: STT s Identity a -> DOTM s a
liftSTT s = DOTM (lift s)

runDOTM :: (forall s. DOTM s a) -> a
runDOTM m = runIdentity $ runSTT $ do
  entryEq <- leastEquiv (:[]) (++)
  exitEq <- leastEquiv (:[]) (++)

  runReaderT (unDOTM m) (entryEq, exitEq)

fastNub :: Ord a => [a] -> [a]
fastNub = Set.toList . Set.fromList

genDOT' :: Constraints -> String
genDOT' = genDOT defaultDOTConfig

genDOT :: DOTConfig -> Constraints -> String
genDOT config constraints =
  runDOTM $ do
    mapM_ combineEntries constraints
    mapM_ combineExits constraints

    let entryExit = getEntryExit constraints
        entries = toList $ entryNodes entryExit
        exits   = toList $ exitNodes  entryExit

    boundaries <- mapM (genBoundaries entries exits) constraints

    connections <- mapM (\(x, y) -> genDOTFor x y) (zip [1..] constraints)

    return $ unlines
      [ "strict digraph {"
      , indent (genConfig config)
      , indent (fastNub (concat boundaries))
      -- , indent (genEntries constraints)
      -- , indent (genExits constraints)
      , indent (concat connections)
      , "}"
      ]

indent :: [String] -> String
indent = unlines . map ("  " <>)

data DOTConfig
  = DOTConfig
    { backgroundColor :: String
    , nodeColor :: String
    , nodeFontColor :: String
    , edgeColor :: String
    , graphMinSize :: Int
    }

defaultDOTConfig :: DOTConfig
defaultDOTConfig =
  DOTConfig
  { backgroundColor = "black"
  , nodeColor = "white"
  , nodeFontColor = "white"
  , edgeColor = "white"
  , graphMinSize = 25
  }

genConfig :: DOTConfig -> [String]
genConfig DOTConfig {..} =
  [ "graph [bgcolor=" <> backgroundColor <> " size=\"" <> show graphMinSize <> "!\"]"
  , "node [color=" <> nodeColor <> " fontcolor=" <> nodeFontColor <> "]"
  , "edge [color=" <> edgeColor <> "]"
  ]

genDOTFor :: Int -> SomeConstraint -> DOTM s [String]
genDOTFor graphN (SomeConstraint sc) = do
  r <- genDOTFor' sc

  return
    [ "subgraph " <> show graphN <> " {"
    , indent r
    , "}"
    ]

data Arrowhead = Forward | Backward

arrowheadAttr :: Arrowhead -> String
arrowheadAttr Forward = "arrowhead=" <> show "empty"
arrowheadAttr Backward = "arrowhead=" <> show "invempty"

-- dotConnect :: NodeId -> NodeId -> String
-- dotConnect (NodeId x) (NodeId y) = dotConnect' (show x) (show y)

dotConnect :: String -> String -> String
dotConnect x y
  | x /= y = x <> " -> " <> y <> ";"
  | x == y = ""

dotConnectWithColor :: String -> String -> String -> String
dotConnectWithColor color x y
  | x /= y = x <> " -> " <> y <> " [color=" <> color <> "];"
  | x == y = ""

-- class BoundaryNodes a where
--   getEntryNodes :: a -> Set NodeId
--   getExitNodes :: a -> Set NodeId

-- instance BoundaryNodes SetConstraint where
--   getEntryNodes (x :=: y) = getEntryNodes x <> getEntryNodes y
--   getExitNodes  (x :=: y) = getExitNodes x <> getExitNodes y

-- instance BoundaryNodes SetConstraints where
--   getEntryNodes = foldr (<>) mempty . map getEntryNodes
--   getExitNodes =  foldr (<>) mempty . map getExitNodes

-- instance BoundaryNodes (SetExpr freeVars) where
--   getEntryNodes (SE_Atom a) = getEntryNodes a
--   getEntryNodes (SE_Union x y) = getEntryNodes x <> getEntryNodes y
--   getEntryNodes (SE_UnionSingle x _ _) = getEntryNodes x
--   getEntryNodes (SE_IfThenElse _ x y) = getEntryNodes x <> getEntryNodes y
--   getEntryNodes SE_Empty = mempty

--   getExitNodes (SE_Atom a) = getExitNodes a
--   getExitNodes (SE_Union x y) = getExitNodes x <> getExitNodes y
--   getExitNodes (SE_UnionSingle x _ _) = getExitNodes x
--   getExitNodes (SE_IfThenElse _ x y) = getExitNodes x <> getExitNodes y
--   getExitNodes SE_Empty = mempty

-- instance BoundaryNodes (AtomicSet freeVars) where
--   getEntryNodes (SingleVar {}) = mempty
--   getEntryNodes (SetFamily sf) = getEntryNodes sf

--   getExitNodes (SingleVar {}) = mempty
--   getExitNodes (SetFamily sf) = getExitNodes sf

-- instance BoundaryNodes (SetFamily freeVars) where
--   getEntryNodes (C_Entry' n) = Set.singleton n
--   getEntryNodes _ = mempty

--   getExitNodes (C_Exit' n) = Set.singleton n
--   getExitNodes _ = mempty

entry :: NodeId -> String
entry (NodeId n) = "entry" <> show n

exit :: NodeId -> String
exit (NodeId n) = "exit" <> show n

node :: NodeId -> String
node (NodeId n) = "n" <> show n

nodeClassName :: (NodeId -> String) -> [NodeId] -> String
nodeClassName f = intercalate "_" . map f

getNodeIds :: IdTracker a -> [NodeId]
getNodeIds = Set.toList . nodeIdsUsed . execWriter . runIdTracker

genBoundaries :: [NodeId] -> [NodeId] -> SomeConstraint -> DOTM s [String]
genBoundaries actualEntries actualExits (SomeConstraint (x :=: y)) = do
  let allNodeIds = toList $ getNodeIds x <> getNodeIds y
      -- actualEntries = toList $ getEntryNodes x <> getEntryNodes y
      -- actualExits = toList $ getExitNodes x <> getExitNodes y

  entryEq <- entryEquiv
  exitEq <- exitEquiv

  -- entries <- liftSTT $ map (nodeClassName entry) <$> mapM (classDesc entryEq) allNodeIds
  -- exits   <- liftSTT $ map (nodeClassName exit)  <$> mapM (classDesc exitEq) allNodeIds

  entries <- liftSTT $ map (nodeClassName entry) <$> mapM (classDesc entryEq) actualEntries
  exits   <- liftSTT $ map (nodeClassName exit)  <$> mapM (classDesc exitEq) actualExits

  fmap (<> map (<> " [shape=box];") (entries ++ exits))
    $ fmap concat
    $ flip mapM allNodeIds
        $ \n -> do
            nEntry <- liftSTT $ nodeClassName entry <$> classDesc entryEq n
            nExit  <- liftSTT $ nodeClassName exit  <$> classDesc exitEq  n

            return
              $  singletonIf (nEntry `dotConnect` node n) (`elem` actualEntries) n
              <> singletonIf (node n `dotConnect` nExit)  (`elem`  actualExits)  n

            -- return $
            --   [ nEntry `dotConnect` node n
            --   , node n `dotConnect` nExit]

  where
    singletonIf :: a -> (b -> Bool) -> b -> [a]
    singletonIf x p y
      | p y = [x]
      | otherwise = []

            -- return $
            --   map (`dotConnect'` (node n)) entries
            --   <> map (dotConnect' (node n)) exits
            --   <> map (<> " [shape=box];") (entries ++ exits)

              -- <> [entry n <> " [shape=box];"]
              -- <> [exit n <> " [shape=box];"]

  -- return $ foldr (<>) mempty $
  --   flip Set.map allNodeIds
  --     $ \n ->
  --         Set.map (`dotConnect'` (node n)) (Set.map entry entries)
  --         <> Set.map (dotConnect' (node n)) (Set.map exit exits)
  --         <> Set.singleton (entry n <> " [shape=box];")
  --         <> Set.singleton (exit n <> " [shape=box];")


-- newtype CombineBoundaries s a = CombineBoundaries (DOTM s ())


combineEntries :: SomeConstraint -> DOTM s ()
combineEntries = undefined
combineExits = undefined

data EntryExit =
  EntryExit
    { entryNodes :: Set NodeId
    , exitNodes  :: Set NodeId
    }

instance Semigroup EntryExit where
  x <> y =
    EntryExit
      { entryNodes = entryNodes x <> entryNodes y
      , exitNodes  = exitNodes  x <> exitNodes  y
      }

instance Monoid EntryExit where
  mempty = EntryExit mempty mempty

newtype EntryExitTracker a = EntryExitTracker { getEntryExitTracker :: Writer EntryExit () }

instance Semigroup (EntryExitTracker a) where
  EntryExitTracker x <> EntryExitTracker y = EntryExitTracker (x >> y)

entryExitRetag :: EntryExitTracker a -> EntryExitTracker b
entryExitRetag (EntryExitTracker x) = EntryExitTracker x

instance BoolExpr EntryExitTracker where
  type EqualCt EntryExitTracker = Unconstrained

  in_ x xs = entryExitRetag (x <> entryExitRetag xs)
  x ^&&^ y = x <> y
  x `equal` y = entryExitRetag (x <> y)
  true = EntryExitTracker $ return ()
  false = EntryExitTracker $ return ()

  ite c t f = entryExitRetag (entryExitRetag c <> t <> f)

instance SetExpr EntryExitTracker where
  type SetCt EntryExitTracker = Unconstrained
  type SetElemCt EntryExitTracker = Unconstrained

  x `union` y = x <> y
  x `unionSingle` y = x <> entryExitRetag y
  empty = EntryExitTracker $ return ()
  setCompr f p s =
    (entryExitRetag (f (EntryExitTracker (return ())))
      <>
     entryExitRetag (p (EntryExitTracker (return ())))
      <>
     entryExitRetag s)

class EntryExitValue a where
  entryExitValue :: a -> EntryExitTracker a

instance EntryExitValue (AnalysisSetFamily a) where
  entryExitValue (C_Entry n) = entryExitRetag $ EntryExitTracker $ tell mempty { entryNodes = [n] }
  entryExitValue (C_Exit n) = entryExitRetag $ EntryExitTracker $ tell mempty { exitNodes = [n] }
  entryExitValue _ = EntryExitTracker $ return ()

instance EntryExitValue (Var, SensExpr) where
  entryExitValue _ = EntryExitTracker $ return ()

instance EntryExitValue Var where
  entryExitValue _ = EntryExitTracker $ return ()

instance EntryExitValue SensExpr where
  entryExitValue _ = EntryExitTracker $ return ()

instance Value EntryExitTracker where
  type ValueCt EntryExitTracker = EntryExitValue
  value = entryExitValue

instance LatticeExpr EntryExitTracker where
  type LatticeCt EntryExitTracker = Unconstrained
  lub x = entryExitRetag x

-- runEntryExitTracker :: Constraints -> EntryExit
-- runEntryExitTracker =

getEntryExit :: Constraints -> EntryExit
getEntryExit = mconcat . map (\(SomeConstraint c) -> go c)
  where
    go :: ConstraintE EntryExitTracker -> EntryExit
    go (EntryExitTracker x :=: EntryExitTracker y) = execWriter x <> execWriter y

-- getExitNodes :: Constraints -> Set NodeId
-- getExitNodes = undefined

newtype GenDOT s a = GenDOT (DOTM s ())

-- instance BoolExpr (GenDOT s) wwhere
--   type EqualCt (GenDOT s) = Unconstrained



genDOTFor' :: GenCs repr => ConstraintE repr -> DOTM s [String]
genDOTFor' = undefined

{-
combineEntries :: SetConstraint -> DOTM s ()
combineEntries (C_Entry' n :=: SE_Atom (C_Entry m)) = do
  entryEq <- entryEquiv

  nClass <- liftSTT $ getClass entryEq n
  mClass <- liftSTT $ getClass entryEq m
  liftSTT $ combine entryEq nClass mClass
  return ()
combineEntries _ = return ()

combineExits :: SetConstraint -> DOTM s ()
combineExits (C_Exit' n :=: SE_Atom (C_Exit m)) =  do
  exitEq <- exitEquiv

  nClass <- liftSTT $ getClass exitEq n
  mClass <- liftSTT $ getClass exitEq m
  liftSTT $ combine exitEq nClass mClass
  return ()
combineExits _ = return ()
-}

-- genConnections :: (String -> String -> String) -> String -> SetExpr freeVars -> DOTM s [String]
-- genConnections connect endpointA e = do
--   let entries0 = toList $ getEntryNodes e
--       exits0 = toList $ getExitNodes e

--   entryEq <- entryEquiv
--   exitEq <- exitEquiv

--   let classDescEntry = classDesc entryEq
--       classDescExit  = classDesc exitEq

--   entries <- liftSTT $ map (nodeClassName entry) <$> mapM classDescEntry entries0
--   exits   <- liftSTT $ map (nodeClassName exit)  <$> mapM classDescExit exits0

--   return $ map (connect endpointA) entries
--            ++ map (connect endpointA) exits

-- genDOTFor' :: SetConstraint -> DOTM s [String]
-- genDOTFor' (C_Entry' n :=: y) = do
--   entryEq <- entryEquiv
--   nDesc <- liftSTT $ classDesc entryEq n
--   genConnections (flip (dotConnectWithColor "red")) (nodeClassName entry nDesc) y

-- genDOTFor' (C_Exit'  n :=: y) = do
--   exitEq <- exitEquiv
--   nDesc <- liftSTT $ classDesc exitEq n

--   genConnections (flip (dotConnectWithColor "red")) (nodeClassName exit nDesc) y
-- genDOTFor' (Atom_E' {} :=: _) = return []
-- genDOTFor' (Atom_S' {} :=: _) = return []

