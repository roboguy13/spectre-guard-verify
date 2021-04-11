module Ppr where

class Ppr a where
  ppr :: a -> String

