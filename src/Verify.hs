{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- {-# OPTIONS_GHC -Wall -Wno-unused-imports #-}

import           Language.C
import           Language.C.Data.Ident

import           Z3.Monad

import           Control.Monad.State
import           Control.Monad.Writer


import           Data.Generics.Uniplate.Data
import           Data.Data

import           Orphans ()

newtype NodeId = NodeId { getNodeId :: Integer }
  deriving (Show, Eq, Data)


newtype ConstraintGen a = ConstraintGen (Writer SetConstraints a)
  deriving (Functor, Applicative, Monad, MonadWriter SetConstraints)

newNodeId :: State NodeId NodeId
newNodeId = do
  NodeId x <- get

  put (NodeId (succ x))

  return $ NodeId x

data Sensitivity = Public | Secret

data SensExpr
  = SensAtom Sensitivity
  | Sens_T NodeId NodeId

data SetConstraint =
  AtomicSet :=: SetExpr

data SetExpr
  = SE_Atom AtomicSet
  | SE_Union SetExpr SetExpr
  | SE_IfThenElse (SensExpr, SensExpr) SetExpr SetExpr

type SetConstraints = [SetConstraint]

data AtomicSet
  = C_Exit NodeId
  | C_Entry NodeId
  | Atom_S NodeId NodeId
  | Single Int SensExpr

class SetExprAtom a where
  c_exit :: NodeId -> a
  c_entry :: NodeId -> a
  atom_s :: NodeId -> NodeId -> a
  single :: Int -> SensExpr -> a

instance SetExprAtom AtomicSet where
  c_exit = C_Exit
  c_entry = C_Entry
  atom_s = Atom_S
  single = Single

instance SetExprAtom SetExpr where
  c_exit = SE_Atom . c_exit
  c_entry = SE_Atom . c_entry
  atom_s x y = SE_Atom (atom_s x y)
  single x y = SE_Atom (single x y)

toLabel :: NodeId -> String
toLabel (NodeId n) = "l" <> show n

unknownLabel :: String
unknownLabel = "l?"

constActionUncurry :: Applicative f => (a -> b -> f ()) -> (a, b) -> f (a, b)
constActionUncurry f (x, y) = f x y *> pure (x, y)

constAction :: Applicative f => (a -> f ()) -> a -> f a
constAction f x = f x *> pure x

isNoSpecAttr :: CAttribute a -> Bool
isNoSpecAttr (CAttr (Ident "nospec" _ _) _ _) = True
isNoSpecAttr _ = False

handleDeclarator :: CDeclarator NodeId -> ConstraintGen ()
handleDeclarator (CDeclr (Just (Ident ident hash _)) _derivs _strLit attrs n)
  | any isNoSpecAttr attrs =
      tell [C_Exit n :=: SE_Union (c_entry n)
                                  (single hash (SensAtom Secret))]

  | otherwise =
      tell [C_Exit n :=: SE_Union (c_entry n)
                                  (single hash (SensAtom Public))]

handleDeclarator _ = pure ()

handleCompoundItem :: CCompoundBlockItem NodeId -> ConstraintGen ()
handleCompoundItem (CBlockDecl (CDecl _ xs _)) = mapM_ go xs
  where
    go (Just declr, _, _) = handleDeclarator declr
    go _ = pure ()
handleCompoundItem (CBlockDecl {}) = pure ()
handleCompoundItem (CBlockStmt stmt) = handleStmt stmt
handleCompoundItem (CNestedFunDef funDef) = handleFunDef funDef

handleExpr :: CExpression NodeId -> ConstraintGen ()
handleExpr = undefined

handleStmt :: CStatement NodeId -> ConstraintGen ()
handleStmt (CIf cond t f_maybe l) = handleExpr cond *> tell go *> handleStmt t *>
    case f_maybe of
      Nothing -> pure ()
      Just f -> handleStmt f
  where
    go =
      [entryConstraint t
      ,C_Exit l :=: SE_IfThenElse (Sens_T l p, SensAtom Secret)
                      (maybeUnion (atom_s l m) (atom_s l))
                      (maybeUnion (c_exit m) c_exit)
      ] ++
        case f_maybe of
          Nothing -> []
          Just f -> [entryConstraint f]

    entryConstraint x = C_Entry (annotation x) :=: SE_Atom (C_Entry l)

    maybeUnion x g =
      case f_maybe of
        Nothing -> x
        Just f -> SE_Union x (g (annotation f))

    p = annotation cond
    m = annotation t

handleStmt (CCompound _ items _) = void $ traverse (constAction handleCompoundItem) items
handleStmt _ = pure ()

handleFunDef :: CFunctionDef NodeId -> ConstraintGen ()
handleFunDef (CFunDef _ _ _ stmt _) = void $ transformM (constAction handleStmt) stmt

handleExtDecl :: CExternalDeclaration NodeId -> ConstraintGen ()
handleExtDecl (CFDefExt funDef) = handleFunDef funDef
handleExtDecl _ = pure ()

handleTransUnit :: (CTranslationUnit NodeId, NodeId) -> ConstraintGen ()
handleTransUnit (CTranslUnit xs _, _) = void $ traverse handleExtDecl xs

main :: IO ()
main = do
  let fileName = "../test.c"

  stream <- readInputStream fileName

  case parseC stream (initPos fileName) of
    Left err -> error (show err)
    Right parsed -> do
      let parsed' = flip runState (NodeId 0) $ traverse (\_ -> newNodeId) parsed
          gen = transformM (constAction handleTransUnit) parsed'

      print parsed

