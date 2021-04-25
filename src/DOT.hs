{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}

module DOT (genDOT, genDOT', DOTConfig(..), defaultDOTConfig) where

import           SetExpr

import           Data.Foldable


genDOT' :: SetConstraints -> String
genDOT' = genDOT defaultDOTConfig

genDOT :: DOTConfig -> SetConstraints -> String
genDOT config constraints =
  unlines
    [ "digraph {"
    , indent (genConfig config)
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
  , graphMinSize = 15
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

dotConnect :: Arrowhead -> NodeId -> NodeId -> String
dotConnect ah (NodeId x) (NodeId y) = show x <> " -> " <> show y <> "[" <> arrowheadAttr ah <> "];"

genDOTFor' :: SetConstraint -> [String]
genDOTFor' (C_Entry' n :=: y) = map (dotConnect Backward n) (toList (getNodeIds y))
genDOTFor' (C_Exit'  n :=: y) = map (dotConnect Forward n) (toList (getNodeIds y))
genDOTFor' (Atom_E'  n :=: y) = map (dotConnect Forward n) (toList (getNodeIds y))
genDOTFor' (Atom_S' {} :=: _) = []

