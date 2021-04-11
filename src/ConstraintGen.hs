{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module ConstraintGen where

import           Language.C
import           Language.C.Data.Ident

import           Control.Monad.Writer
import           Data.Generics.Uniplate.Data

import           SetExpr


newtype ConstraintGen a = ConstraintGen (Writer SetConstraints a)
  deriving (Functor, Applicative, Monad, MonadWriter SetConstraints)

execConstraintGen :: ConstraintGen a -> SetConstraints
execConstraintGen (ConstraintGen g) = execWriter g

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
handleCompoundItem (CBlockStmt stmt) = pure () --handleStmt stmt
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

handleStmt e = pure () --mapM_ handleStmt $ drop 1 $ universe e

handleFunDef :: CFunctionDef NodeId -> ConstraintGen ()
handleFunDef (CFunDef _ _ _ stmt _) = void $ transformM (constAction handleStmt) stmt

handleExtDecl :: CExternalDeclaration NodeId -> ConstraintGen ()
handleExtDecl (CFDefExt funDef) = handleFunDef funDef
handleExtDecl _ = pure ()

handleTransUnit :: (CTranslationUnit NodeId, NodeId) -> ConstraintGen ()
handleTransUnit (CTranslUnit xs _, _) = void $ traverse handleExtDecl xs

