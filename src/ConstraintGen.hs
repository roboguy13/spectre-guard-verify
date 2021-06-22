{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}

{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

module ConstraintGen where

import           Language.C
import           Language.C.Data.Ident

import           Data.Data

import           Data.Constraint

import           Control.Monad.Writer
import           Data.Generics.Uniplate.Data

import           Data.Maybe

import           SetExpr

newtype Var = Var { getVar :: Int }
  deriving (Show, Eq, Ord, Data)

newtype NodeId = NodeId { getNodeId :: Integer }
  deriving (Show, Eq, Ord, Data)

data Sensitivity = Public | Secret
  deriving (Show, Eq)

data SensExpr where
  SensAtom :: Sensitivity -> SensExpr
  SensT :: NodeId -> SensExpr

-- | The set family for this analysis
data AnalysisSetFamily a where
  C_Entry :: NodeId -> AnalysisSetFamily (Var, SensExpr)
  C_Exit :: NodeId -> AnalysisSetFamily (Var, SensExpr)

  S_Family :: NodeId -> NodeId -> AnalysisSetFamily (Var, SensExpr)
  B_Family :: NodeId -> AnalysisSetFamily Var

type Constraints repr = [ConstraintE repr]


newtype ConstraintGen repr a = ConstraintGen (Writer (Constraints repr) a)
  deriving (Functor, Applicative, Monad, MonadWriter (Constraints repr))

type GenCs repr = (Expr repr, EqualCt repr SensExpr, SetCt repr AnalysisSetFamily, SetElemCt repr (Var, SensExpr), LatticeCt repr SensExpr, ValueCt repr (Var, SensExpr), ValueCt repr (AnalysisSetFamily (Var, SensExpr)), ValueCt repr SensExpr)
  :: Constraint


execConstraintGen :: ConstraintGen repr a -> Constraints repr
execConstraintGen (ConstraintGen g) = execWriter g

constAction :: Applicative f => (a -> f ()) -> a -> f a
constAction f x = f x *> pure x

isNoSpecAttr :: Show a => CAttribute a -> Bool
isNoSpecAttr (CAttr (Ident "nospec" _ _) _ _) = True
isNoSpecAttr _ = False

handleDeclarator :: (GenCs repr) => CDeclarator NodeId -> ConstraintGen repr ()
handleDeclarator e@(CDeclr (Just (Ident ident hash _)) _derivs _strLit attrs n)
  | any isNoSpecAttr attrs = do
      mapM_ (sameNode e) attrs

      tell [setValue (C_Exit n) :=: unionSingle (setValue (C_Entry n)) (value (Var hash, SensAtom Secret))]

  | otherwise = do
      mapM_ (sameNode e) attrs
      tell [setValue (C_Exit n) :=: unionSingle (setValue (C_Entry n)) (value (Var hash, (SensAtom Public)))]

handleDeclarator e = nop e

handleCompoundItem :: (GenCs repr) => CCompoundBlockItem NodeId -> ConstraintGen repr ()
handleCompoundItem (CBlockDecl e@(CDecl _ [] _)) = nop e
handleCompoundItem (CBlockDecl e@(CDecl declSpec xs _)) = do
    -- nop e

    mapM_ (sameNode e) declSpec

    -- mapM_ (sameNode e) $ catMaybes $ map (\(z, _, _) -> z) xs

    -- case catMaybes $ map (\(z, _, _) -> z) xs of
    --   [] -> pure ()
    --   xs'@(x:_) -> do
    --     e `connect` x
    --     connectList xs'

    mapM_ go xs
  where
    go (Just declr, _, _) = sameNode e declr *> handleDeclarator declr
    go _ = pure ()
-- handleCompoundItem (CBlockDecl {}) = pure ()
handleCompoundItem (CBlockDecl e) = nop e
handleCompoundItem (CBlockStmt stmt) = handleStmt stmt -- pure ()
handleCompoundItem (CNestedFunDef funDef) = handleFunDef funDef

handleExpr :: (GenCs repr) => CExpression NodeId -> ConstraintGen repr ()
handleExpr e0@(CAssign _ cv@(CVar (Ident _ x _) _) e n) = do
  let m = annotation e

  e0 `connect` e

  handleExpr cv
  tell [ setValue (C_Exit n) :=: ite (in_ (value (Var x, SensAtom Public)) (value (C_Entry n)))
                                    (unionSingle (value (C_Entry n)) (value (Var x, (SensT (annotation e)))))
                                    (value (C_Entry n))
       ]
    *> handleExpr e

handleExpr e@(CVar (Ident _ x _) _) = return ()

handleExpr expr = do
  nop expr
  let theChildren = children expr

  forM_ theChildren $ \c -> do
    -- tell [ c_entry (annotation c) :=: c_exit (annotation expr) ]
    sameNode c expr
    handleExpr c
  -- mapM_ handleExpr $ children expr
  -- go nodeIds
  where
    exprNodeId = annotation expr

handleStmt :: (GenCs repr) => CStatement NodeId -> ConstraintGen repr ()
handleStmt e0@(CExpr (Just e) _) = do
  nop e0
  e0 `connect` e
  handleExpr e
handleStmt e0@(CIf cond t f_maybe l) = do
  handleExpr cond

  -- e0 `connect` cond
  tell [ setValue (C_Entry (annotation cond)) :=: value (C_Entry l) ]

  tell go

  handleStmt t

  -- tell [atom_e (annotation e0) :=: atom_e (annotation cond)]

  case f_maybe of
    Nothing -> pure ()
    Just f -> handleStmt f
  where
    go =
      [entryConstraint t
      ,setValue (C_Exit l) :=: union (value (C_Entry l))
                             (ite (value (SensT l) `equal` value (SensAtom Secret))
                               (maybeUnion (S_Family l m) (S_Family l))
                               (maybeUnion (C_Exit m) C_Exit))
      ] ++
        case f_maybe of
          Nothing -> []
          Just f -> [entryConstraint f]

    entryConstraint x = setValue (C_Entry (annotation x)) :=: value (C_Entry l)

    maybeUnion x g =
      case f_maybe of
        Nothing -> value x
        Just f -> union (value x) (value (g (annotation f)))

    p = annotation cond
    m = annotation t

handleStmt e@(CCompound _ items _) = do
  nop e

  case items of
    [] -> pure ()
    (firstItem:_) -> --tell [ c_entry (annotation firstItem) :=: c_exit (annotation e) ]
      e `connect` firstItem

  connectList items
  mapM_ handleCompoundItem items

handleStmt e = do --pure () --mapM_ handleStmt $ drop 1 $ universe e -- pure ()
  nop e

  case children e of
    [] -> pure ()
    cs@(c:_) -> do
      e `connect` c

      connectList cs

      mapM_ handleStmt cs

-- | Generate C_Exit(n) = C_Entry(n) constraint for given node
nop :: (GenCs repr, Annotated f) => f NodeId -> ConstraintGen repr ()
nop e =
  tell
    [ setValue (C_Exit (annotation e)) :=: value (C_Entry (annotation e)) ]

connectList :: (GenCs repr, Annotated f) => [f NodeId] -> ConstraintGen repr ()
connectList [] = pure ()
connectList [_] = pure ()
connectList (x:y:rest) = do
  connect x y
  connectList (y:rest)

connect :: (GenCs repr, Annotated f, Annotated g) => f NodeId -> g NodeId -> ConstraintGen repr ()
connect x y =
  tell
    [ setValue (C_Entry (annotation y)) :=: value (C_Exit (annotation x)) ]

-- | Combine two nodes, to behave as one
sameNode :: (GenCs repr, Annotated f, Annotated g) => f NodeId -> g NodeId -> ConstraintGen repr ()
sameNode x y =
  tell
    [ setValue (C_Entry (annotation x)) :=: value (C_Entry (annotation y))
    , setValue (C_Exit  (annotation x)) :=: value (C_Exit  (annotation y))
    ]

-- TODO: Connect to following nodes
handleFunDef :: (GenCs repr) => CFunctionDef NodeId -> ConstraintGen repr ()
handleFunDef e@(CFunDef _ _ _ stmt _) = do
  tell
    [ setValue (C_Exit (annotation e)) :=: empty
    , setValue (C_Entry (annotation stmt)) :=: value (C_Exit (annotation e))
    ]
  void $ (constAction handleStmt) stmt

handleExtDecl :: (GenCs repr) => CExternalDeclaration NodeId -> ConstraintGen repr ()
handleExtDecl (CFDefExt funDef) = handleFunDef funDef
handleExtDecl _ = pure ()

handleTransUnit :: (GenCs repr) => (CTranslationUnit NodeId, NodeId) -> ConstraintGen repr ()
handleTransUnit (CTranslUnit xs _, _) = void $ traverse handleExtDecl xs

