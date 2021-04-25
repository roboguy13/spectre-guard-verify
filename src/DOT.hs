{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}

module DOT (genDOT, genDOT', DOTConfig(..), defaultDOTConfig) where

import           SetExpr

import           Data.Foldable
import           Data.Set (Set)
import qualified Data.Set as Set


genDOT' :: SetConstraints -> String
genDOT' = genDOT defaultDOTConfig

genDOT :: DOTConfig -> SetConstraints -> String
genDOT config constraints =
  unlines
    [ "digraph {"
    , indent (genConfig config)
    , indent (toList (foldr (<>) mempty (map genBoundaries constraints)))
    -- , indent (genEntries constraints)
    -- , indent (genExits constraints)
    , indent (concatMap (uncurry genDOTFor) (zip [1..] constraints))
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
  , graphMinSize = 45
  }

genConfig :: DOTConfig -> [String]
genConfig DOTConfig {..} =
  [ "graph [bgcolor=" <> backgroundColor <> " size=\"" <> show graphMinSize <> "!\"]"
  , "node [color=" <> nodeColor <> " fontcolor=" <> nodeFontColor <> "]"
  , "edge [color=" <> edgeColor <> "]"
  ]

genDOTFor :: Int -> SetConstraint -> [String]
genDOTFor graphN sc =
  [ "subgraph " <> show graphN <> " {"
  , indent (genDOTFor' sc)
  , "}"
  ]

data Arrowhead = Forward | Backward

arrowheadAttr :: Arrowhead -> String
arrowheadAttr Forward = "arrowhead=" <> show "empty"
arrowheadAttr Backward = "arrowhead=" <> show "invempty"

dotConnect :: NodeId -> NodeId -> String
dotConnect (NodeId x) (NodeId y) = dotConnect' (show x) (show y)

dotConnect' :: String -> String -> String
dotConnect' x y = x <> " -> " <> y <> ";"

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

genBoundaries :: SetConstraint -> Set String
genBoundaries (x :=: y) =
  let allNodeIds = getNodeIds x <> getNodeIds y
      entries = getEntryNodes x <> getEntryNodes y
      exits = getExitNodes x <> getExitNodes y
  in
    foldr (<>) mempty $
    flip Set.map allNodeIds
      $ \n ->
          Set.map (`dotConnect'` (node n)) (Set.map entry entries)
          <> Set.map (dotConnect' (node n)) (Set.map exit exits)
          <> Set.singleton (entry n <> " [shape=box];")
          <> Set.singleton (exit n <> " [shape=box];")



genConnections :: (String -> String -> String) -> String -> SetExpr freeVars -> [String]
genConnections connect endpointA e =
  let entries = toList $ getEntryNodes e
      exits = toList $ getExitNodes e
  in
  map (connect endpointA) (map entry entries)
  ++ map (connect endpointA) (map exit exits)

genDOTFor' :: SetConstraint -> [String]
-- genDOTFor' = undefined
-- -- genDOTFor' (C_Entry' n :=: y) = 
genDOTFor' (C_Entry' n :=: y) = genConnections (flip dotConnect') (entry n) y
genDOTFor' (C_Exit'  n :=: y) = genConnections dotConnect' (exit n) y
-- genDOTFor' (Atom_E'  n :=: y) = map (dotConnect n) (toList (getNodeIds y))
genDOTFor' (Atom_E' {} :=: _) = []
genDOTFor' (Atom_S' {} :=: _) = []

