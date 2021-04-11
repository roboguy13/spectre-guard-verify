{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

-- {-# OPTIONS_GHC -Wall -Wno-unused-imports #-}

import           Language.C
import           Language.C.Data.Ident

import           Z3.Monad

import           Control.Monad.State
import           Control.Monad.Writer


import           Data.Generics.Uniplate.Data
import           Data.Data

import           Data.Bifunctor

import           Orphans ()
import           Ppr
import           SetExpr
import           ConstraintGen

nodeIdToLoc :: CTranslationUnit (NodeInfo, NodeId) -> NodeId -> (NodeId, Maybe Position)
nodeIdToLoc transUnit nodeId =
  (nodeId, fmap posOf . lookup nodeId $ foldMap (\(info, nodeId') -> [(nodeId', info)]) transUnit)

nodeIdLocInfo :: [(NodeId, Maybe Position)] -> String
nodeIdLocInfo = unlines . map go
  where
    go (nodeId, pos_maybe) = ppr nodeId ++ ": " ++
      case pos_maybe of
        Nothing -> "<no position info>"
        Just pos -> show pos

getAnns :: CTranslationUnit a -> [a]
getAnns = foldMap (:[])

main :: IO ()
main = do
  let fileName = "../test.c"

  stream <- readInputStream fileName

  case parseC stream (initPos fileName) of
    Left err -> error (show err)
    Right parsed -> do
      let parsed' = flip runState (NodeId 0) $ traverse (\x -> (x,) <$> newNodeId) parsed
          parsed'' = first (fmap snd) parsed'
          constraints = execConstraintGen $ transformM (constAction handleTransUnit) parsed''
          nodeInfo = map (nodeIdToLoc (fst parsed')) (getAnns (fst parsed''))

      putStrLn $ ppr constraints
      putStrLn (nodeIdLocInfo nodeInfo)
      print parsed'

