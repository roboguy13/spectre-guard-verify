{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}

module DOT (genDOT, genDOT', DOTConfig(..), defaultDOTConfig) where

import           SetExpr

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

genDOT' :: SetConstraints -> String
genDOT' = genDOT defaultDOTConfig

genDOT :: DOTConfig -> SetConstraints -> String
genDOT config constraints =
  runDOTM $ do
    mapM_ combineEntries constraints
    mapM_ combineExits constraints
    boundaries <- mapM genBoundaries constraints

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

genDOTFor :: Int -> SetConstraint -> DOTM s [String]
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

dotConnect :: NodeId -> NodeId -> String
dotConnect (NodeId x) (NodeId y) = dotConnect' (show x) (show y)

dotConnect' :: String -> String -> String
dotConnect' x y
  | x /= y = x <> " -> " <> y <> ";"
  | x == y = ""

class BoundaryNodes a where
  getEntryNodes :: a -> Set NodeId
  getExitNodes :: a -> Set NodeId

instance BoundaryNodes (SetExpr freeVars) where
  getEntryNodes (SE_Atom a) = getEntryNodes a
  getEntryNodes (SE_Union x y) = getEntryNodes x <> getEntryNodes y
  getEntryNodes (SE_UnionSingle x _ _) = getEntryNodes x
  getEntryNodes (SE_IfThenElse _ x y) = getEntryNodes x <> getEntryNodes y
  getEntryNodes SE_Empty = mempty

  getExitNodes (SE_Atom a) = getExitNodes a
  getExitNodes (SE_Union x y) = getExitNodes x <> getExitNodes y
  getExitNodes (SE_UnionSingle x _ _) = getExitNodes x
  getExitNodes (SE_IfThenElse _ x y) = getExitNodes x <> getExitNodes y
  getExitNodes SE_Empty = mempty

instance BoundaryNodes (AtomicSet freeVars) where
  getEntryNodes (SingleVar {}) = mempty
  getEntryNodes (SetFamily sf) = getEntryNodes sf

  getExitNodes (SingleVar {}) = mempty
  getExitNodes (SetFamily sf) = getExitNodes sf

instance BoundaryNodes (SetFamily freeVars) where
  getEntryNodes (C_Entry' n) = Set.singleton n
  getEntryNodes _ = mempty

  getExitNodes (C_Exit' n) = Set.singleton n
  getExitNodes _ = mempty

entry :: NodeId -> String
entry (NodeId n) = "entry" <> show n

exit :: NodeId -> String
exit (NodeId n) = "exit" <> show n

node :: NodeId -> String
node (NodeId n) = "n" <> show n

nodeClassName :: (NodeId -> String) -> [NodeId] -> String
nodeClassName f = intercalate "_" . map f

genBoundaries :: SetConstraint -> DOTM s [String]
genBoundaries (x :=: y) = do
  let allNodeIds = toList $ getNodeIds x <> getNodeIds y
      entries0 = toList $ getEntryNodes x <> getEntryNodes y
      exits0 = toList $ getExitNodes x <> getExitNodes y

  entryEq <- entryEquiv
  exitEq <- exitEquiv

  entries <- liftSTT $ map (nodeClassName entry) <$> mapM (classDesc entryEq) entries0
  exits   <- liftSTT $ map (nodeClassName exit)  <$> mapM (classDesc exitEq) exits0

  return $
    fmap concat $ flip mapM allNodeIds
        $ \n -> do
            -- theEntry <-
            map (`dotConnect'` (node n)) entries
            <> map (dotConnect' (node n)) exits
            <> map (<> " [shape=box];") (entries ++ exits)
            -- <> [entry n <> " [shape=box];"]
            -- <> [exit n <> " [shape=box];"]

  -- return $ foldr (<>) mempty $
  --   flip Set.map allNodeIds
  --     $ \n ->
  --         Set.map (`dotConnect'` (node n)) (Set.map entry entries)
  --         <> Set.map (dotConnect' (node n)) (Set.map exit exits)
  --         <> Set.singleton (entry n <> " [shape=box];")
  --         <> Set.singleton (exit n <> " [shape=box];")

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

genConnections :: (String -> String -> String) -> String -> SetExpr freeVars -> DOTM s [String]
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

genDOTFor' :: SetConstraint -> DOTM s [String]
genDOTFor' (C_Entry' n :=: y) = do
  entryEq <- entryEquiv
  nDesc <- liftSTT $ classDesc entryEq n
  genConnections (flip dotConnect') (nodeClassName entry nDesc) y

genDOTFor' (C_Exit'  n :=: y) = do
  exitEq <- exitEquiv
  nDesc <- liftSTT $ classDesc exitEq n

  genConnections dotConnect' (nodeClassName exit nDesc) y
genDOTFor' (Atom_E' {} :=: _) = return []
genDOTFor' (Atom_S' {} :=: _) = return []

