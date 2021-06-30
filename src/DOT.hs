{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

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

genDOT' :: Constraints r -> String
genDOT' = genDOT defaultDOTConfig

genDOT :: DOTConfig -> Constraints r -> String
genDOT config constraints =
  runDOTM $ do
    mapM_ combineEntries constraints
    mapM_ combineExits constraints

    let entries = toList $ getEntryNodes constraints
        exits   = toList $ getExitNodes constraints

    boundaries <- mapM (genBoundaries entries exits) constraints

    connections <- mapM (uncurry genDOTFor) (zip [1..] constraints)

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

genDOTFor :: Int -> AnalysisConstraint r -> DOTM s [String]
genDOTFor graphN sc = do
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

class BoundaryNodes a where
  getEntryNodes :: a -> Set NodeId
  getExitNodes :: a -> Set NodeId

instance BoundaryNodes (AnalysisConstraint r) where
  getEntryNodes c = withConstraintSides c $ \(x, y) -> getEntryNodes x <> getEntryNodes y
  getExitNodes  c = withConstraintSides c $ \(x, y) -> getExitNodes x <> getExitNodes y

instance BoundaryNodes (Constraints r) where
  getEntryNodes = foldr (<>) mempty . map getEntryNodes
  getExitNodes =  foldr (<>) mempty . map getExitNodes

instance BoundaryNodes (AnalysisExpr r a) where
  getEntryNodes (SetFamily a) = getEntryNodes a
  getEntryNodes (Union x y) = getEntryNodes x <> getEntryNodes y
  getEntryNodes (UnionSingle x _) = getEntryNodes x
  getEntryNodes (Ite _ x y) = getEntryNodes x <> getEntryNodes y
  getEntryNodes Empty = mempty

  getExitNodes (SetFamily a) = getExitNodes a
  getExitNodes (Union x y) = getExitNodes x <> getExitNodes y
  getExitNodes (UnionSingle x _) = getExitNodes x
  getExitNodes (Ite _ x y) = getExitNodes x <> getExitNodes y
  getExitNodes Empty = mempty

instance BoundaryNodes (AnalysisSetFamily a) where
  getEntryNodes (C_Entry n) = Set.singleton n
  getEntryNodes _ = mempty

  getExitNodes (C_Exit n) = Set.singleton n
  getExitNodes _ = mempty

entry :: NodeId -> String
entry (NodeId n) = "entry" <> show n

exit :: NodeId -> String
exit (NodeId n) = "exit" <> show n

node :: NodeId -> String
node (NodeId n) = "n" <> show n

nodeClassName :: (NodeId -> String) -> [NodeId] -> String
nodeClassName f = intercalate "_" . map f

genBoundaries :: [NodeId] -> [NodeId] -> AnalysisConstraint r -> DOTM s [String]
genBoundaries actualEntries actualExits c = withConstraintSides c $ \(x, y) -> do
  let allNodeIds = toList $ nodeIdsUsed $ getUsedIds' c
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

combineEntries :: AnalysisConstraint r -> DOTM s ()
combineEntries (SetFamily (C_Entry n) :=: SetFamily (C_Entry m)) = do
  entryEq <- entryEquiv

  nClass <- liftSTT $ getClass entryEq n
  mClass <- liftSTT $ getClass entryEq m
  liftSTT $ combine entryEq nClass mClass
  return ()
combineEntries _ = return ()

combineExits :: AnalysisConstraint r -> DOTM s ()
combineExits (SetFamily (C_Exit n) :=: SetFamily (C_Exit m)) =  do
  exitEq <- exitEquiv

  nClass <- liftSTT $ getClass exitEq n
  mClass <- liftSTT $ getClass exitEq m
  liftSTT $ combine exitEq nClass mClass
  return ()
combineExits _ = return ()

genConnections :: (String -> String -> String) -> String -> AnalysisExpr r a -> DOTM s [String]
genConnections connect endpointA e = do
  let entries0 = toList $ getEntryNodes e
      exits0 = toList $ getExitNodes e

  entryEq <- entryEquiv
  exitEq <- exitEquiv

  let classDescEntry = classDesc entryEq
      classDescExit  = classDesc exitEq

  entries <- liftSTT $ map (nodeClassName entry) <$> mapM classDescEntry entries0
  exits   <- liftSTT $ map (nodeClassName exit)  <$> mapM classDescExit exits0

  return $ map (connect endpointA) entries
           ++ map (connect endpointA) exits

genEmpty :: NodeId -> (NodeId -> String) -> DOTM s [String]
genEmpty n nodeName = do
  entryEq <- entryEquiv
  nDesc <- liftSTT $ classDesc entryEq n
  return [dotConnectWithColor "red" (show "{ }") (nodeClassName nodeName nDesc)]

constraintColor :: AnalysisConstraint r -> String
constraintColor (_ :=: _) = "red"
constraintColor (_ :<: _) = "blue"

genDOTFor' :: AnalysisConstraint r -> DOTM s [String]
genDOTFor' c = withConstraintSides c $ \p ->
  case p of
    (SetFamily (C_Entry n), Empty) -> genEmpty n entry
    (SetFamily (C_Exit n), Empty) -> genEmpty n exit
    (SetFamily (C_Entry n), y) -> do
      entryEq <- entryEquiv
      nDesc <- liftSTT $ classDesc entryEq n

      genConnections (flip (dotConnectWithColor (constraintColor c))) (nodeClassName entry nDesc) y

    (SetFamily (C_Exit n), y) -> do
      exitEq <- exitEquiv
      nDesc <- liftSTT $ classDesc exitEq n

      genConnections (flip (dotConnectWithColor (constraintColor c))) (nodeClassName exit nDesc) y
    (SetFamily (E_Family {}), _) -> return []
    (SetFamily (S_Family {}), _) -> return []
    (_, _) -> return []

