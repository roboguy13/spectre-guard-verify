{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}

module ValidNodeId
  (ValidNodeId
  ,pattern ValidNodeId
  ,getValidNodeId

  ,ValidNodeIdPair
  ,pattern ValidNodeIdPair
  ,getValidNodeIdPair

  ,eNodeIds
  ,tNodeIds
  ,sNodeIdPairs
  )
  where

import           ConstraintGen

import           Data.Foldable
import           Data.Coerce

newtype ValidNodeId p = MkValidNodeId { getValidNodeId :: NodeId }

newtype ValidNodeIdPair p = MkValidNodeIdPair { getValidNodeIdPair :: (NodeId, NodeId) }

  -- | Allowed to match on, but not allowed to construct
pattern ValidNodeId x <- MkValidNodeId x

  -- | Allowed to match on, but not allowed to construct
pattern ValidNodeIdPair x <- MkValidNodeIdPair x

eNodeIds :: UsedIds -> [ValidNodeId E_Family]
eNodeIds = coerce . toList . eNodesUsed

tNodeIds :: UsedIds -> [ValidNodeId SensT]
tNodeIds = coerce . toList . tNodesUsed

sNodeIdPairs :: UsedIds -> [ValidNodeIdPair S_Family]
sNodeIdPairs = coerce . toList . sPairsUsed

entryNodeIds :: UsedIds -> [ValidNodeId C_Entry]
entryNodeIds = coerce . toList . nodeIdsUsed

exitNodeIds :: UsedIds -> [ValidNodeId C_Exit]
exitNodeIds = coerce . toList . nodeIdsUsed

