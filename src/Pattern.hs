-- This is a simplified, restricted version of https://github.com/roboguy13/patterns

{-# LANGUAGE GADTs #-}

module Pattern where

data Pattern f s t where
  BasePat :: Pattern f (f a) a
  PairPat :: Pattern f (f (a, b)) (f a, f b)

data Match f s t where
  (:->) :: Pattern f s t -> (s -> t) -> Match f s t

