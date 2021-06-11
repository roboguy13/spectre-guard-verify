-- This is a simplified, restricted version of https://github.com/roboguy13/patterns

{-# LANGUAGE GADTs #-}

module Pattern where

data Pattern s where
  BasePat :: Pattern a
  PairPat :: Pattern (a, b)

data Match s t where
  (:->) :: Pattern s -> (s -> t) -> Match s t

