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

import           Orphans ()

newtype NodeId = NodeId { getNodeId :: Integer }
  deriving (Show, Eq, Data)


newtype ConstraintGen a = ConstraintGen (Writer SetConstraints a)
  deriving (Functor, Applicative, Monad, MonadWriter SetConstraints)

execConstraintGen :: ConstraintGen a -> SetConstraints
execConstraintGen (ConstraintGen g) = execWriter g

newNodeId :: State NodeId NodeId
newNodeId = do
  NodeId x <- get

  put (NodeId (succ x))

  return $ NodeId x

class Ppr a where
  ppr :: a -> String

instance Ppr NodeId where
  ppr = show . getNodeId

data Sensitivity = Public | Secret
  deriving (Show)

instance Ppr Sensitivity where ppr = show

data SensExpr
  = SensAtom Sensitivity
  | Sens_T NodeId NodeId
  deriving (Show)

instance Ppr SensExpr where
  ppr (SensAtom x) = ppr x
  ppr (Sens_T x y) = "T(" ++ ppr x ++ ", " ++ ppr y ++ ")"

data SetConstraint =
  AtomicSet :=: SetExpr
  deriving (Show)

instance Ppr SetConstraint where
  ppr (x :=: y) = ppr x ++ " = " ++ ppr y

data SetExpr
  = SE_Atom AtomicSet
  | SE_Union SetExpr SetExpr
  | SE_IfThenElse (SensExpr, SensExpr) SetExpr SetExpr
  deriving (Show)

instance Ppr SetExpr where
  ppr (SE_Atom x) = ppr x
  ppr (SE_Union x y) = "(" ++ ppr x ++ ") U (" ++ ppr y ++ ")"
  ppr (SE_IfThenElse (x,y) t f) = "if (" ++ ppr x ++ " = " ++ ppr y ++ ") then " ++ ppr t ++ " else " ++ ppr f

type SetConstraints = [SetConstraint]

data AtomicSet
  = C_Exit NodeId
  | C_Entry NodeId
  | Atom_S NodeId NodeId
  | Atom_E NodeId
  | Single Int SensExpr
  | SingleVar Int
  deriving (Show)

instance Ppr AtomicSet where
  ppr (C_Exit n) = "C_exit(" ++ ppr n ++ ")"
  ppr (C_Entry n) = "C_entry(" ++ ppr n ++ ")"
  ppr (Atom_S x y) = "S(" ++ ppr x ++ ", " ++ ppr y ++ ")"
  ppr (Atom_E x) = "E(" ++ ppr x ++ ")"
  ppr (Single x y) = "{(" ++ show x ++ ", " ++ ppr y ++ ")}"
  ppr (SingleVar v) = show v

instance Ppr SetConstraints where
  ppr = unlines . map ppr

class SetExprAtom a where
  c_exit :: NodeId -> a
  c_entry :: NodeId -> a
  atom_s :: NodeId -> NodeId -> a
  atom_e :: NodeId -> a
  single :: Int -> SensExpr -> a
  singleVar :: Int -> a

instance SetExprAtom AtomicSet where
  c_exit = C_Exit
  c_entry = C_Entry
  atom_s = Atom_S
  atom_e = Atom_E
  single = Single
  singleVar = SingleVar

instance SetExprAtom SetExpr where
  c_exit = SE_Atom . c_exit
  c_entry = SE_Atom . c_entry
  atom_s x y = SE_Atom (atom_s x y)
  atom_e = SE_Atom . atom_e
  single x y = SE_Atom (single x y)
  singleVar = SE_Atom . singleVar

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
handleExpr (CAssign CAssignOp (CVar (Ident _ x _) _) e n) =
  let m = annotation e
  in
  tell [ c_exit n :=: (c_entry n `SE_Union` single x (Sens_T n m)) ]
    *> handleExpr e

handleExpr expr =
  case expr of
    CVar (Ident _ v _) _ -> tell [ Atom_E exprNodeId :=: singleVar v ]
    _ ->
      case nodeIds of
        [] -> pure ()
        (x:xs) ->
          tell [
              Atom_E exprNodeId :=: foldr SE_Union x xs
            ]
  where
    exprNodeId = annotation expr

    nodeIds = map (atom_e . annotation) . drop 1 $ universe expr

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

handleStmt (CCompound _ items _) = do
  void $ traverse (constAction handleCompoundItem) items
  go items
  where
    go [] = pure ()
    go [_] = pure ()
    go (x:y:rest) = do
      tell [ c_entry (annotation y) :=: c_exit (annotation x) ]
      go (y:rest)

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
          constraints = execConstraintGen $ transformM (constAction handleTransUnit) parsed'

      putStrLn $ ppr constraints

