{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC -Wall -Wno-unused-imports #-}

import           Language.C

import           Control.Monad.State

import           Orphans ()

newtype NodeId = NodeId { getNodeId :: Integer }
  deriving (Show, Eq)

newNodeId :: State NodeId NodeId
newNodeId = do
  NodeId x <- get

  put (NodeId (succ x))

  return $ NodeId x

main :: IO ()
main = do
  let fileName = "../test.c"

  stream <- readInputStream fileName

  case parseC stream (initPos fileName) of
    Left err -> error (show err)
    Right parsed -> do
      let parsed' = flip runState (NodeId 0) $ traverse (const newNodeId) parsed

      print parsed'

