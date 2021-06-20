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

-- pattern C_Entry' n = SetFamily (C_Entry n)
-- pattern C_Exit' n = SetFamily (C_Exit n)
-- pattern S_Family' m n = SetFamily (S_Family m n)
-- pattern B_Family' n = SetFamily (B_Family n)

-- class AnalysisSfExpr f where
--   c_entry :: NodeId -> f (Var, SensExpr c)
--   c_exit  :: NodeId -> f (Var, SensExpr c)

--   s_family :: NodeId -> NodeId -> f (Var, SensExpr c)
--   b_family :: NodeId -> f Var

-- instance AnalysisSfExpr (AnalysisSetFamily c) where
--   c_entry = C_Entry
--   c_exit = C_Exit
--   s_family n = S n
--   b_family = B

-- instance AnalysisSfExpr (SetExpr c (AnalysisSetFamily c)) where
--   c_entry = SetFamily . c_entry
--   c_exit = SetFamily . c_exit
--   s_family n = SetFamily . s_family n
--   b_family = SetFamily . b_family

type Constraints valueC repr = [ConstraintE AnalysisSetFamily SensExpr valueC repr]


newtype ConstraintGen valueC repr a = ConstraintGen (Writer (Constraints valueC repr) a)
  deriving (Functor, Applicative, Monad, MonadWriter (Constraints valueC repr))


execConstraintGen :: ConstraintGen valueC repr a -> Constraints valueC repr
execConstraintGen (ConstraintGen g) = execWriter g

constAction :: Applicative f => (a -> f ()) -> a -> f a
constAction f x = f x *> pure x

isNoSpecAttr :: Show a => CAttribute a -> Bool
isNoSpecAttr (CAttr (Ident "nospec" _ _) _ _) = True
isNoSpecAttr _ = False

handleDeclarator :: () => CDeclarator NodeId -> ConstraintGen valueC repr ()
handleDeclarator e@(CDeclr (Just (Ident ident hash _)) _derivs _strLit attrs n)
  | any isNoSpecAttr attrs = do
      mapM_ (sameNode e) attrs

      tell [C_Exit n :=: unionSingle (C_Entry n) (value (Var hash, SensAtom Secret))]

  | otherwise = do
      mapM_ (sameNode e) attrs
      tell [C_Exit n :=: unionSingle (C_Entry n) (Var hash, (SensAtom Public))]

handleDeclarator e = nop e

handleCompoundItem :: () => CCompoundBlockItem NodeId -> ConstraintGen valueC repr ()
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

handleExpr :: () => CExpression NodeId -> ConstraintGen valueC repr ()
handleExpr e0@(CAssign _ cv@(CVar (Ident _ x _) _) e n) = do
  let m = annotation e

  e0 `connect` e

  handleExpr cv
  tell [ C_Exit n :=: ite (In' (Var x, SensAtom Public) (C_Entry n))
                                    (unionSingle (C_Entry n) (Var x, (SensFamily (SensT (annotation e)))))
                                    (C_Entry n)
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

handleStmt :: () => CStatement NodeId -> ConstraintGen valueC repr ()
handleStmt e0@(CExpr (Just e) _) = do
  nop e0
  e0 `connect` e
  handleExpr e
handleStmt e0@(CIf cond t f_maybe l) = do
  handleExpr cond

  -- e0 `connect` cond
  tell [ C_Entry (annotation cond) :=: (C_Entry l) ]

  tell go

  handleStmt t

  -- tell [atom_e (annotation e0) :=: atom_e (annotation cond)]

  case f_maybe of
    Nothing -> pure ()
    Just f -> handleStmt f
  where
    go =
      [entryConstraint t
      ,C_Exit l :=: union (C_Entry l)
                             (ite (SensFamily (SensT l) `LatticeEqual` SensAtom Secret)
                               (maybeUnion (S_Family' l m) (S_Family' l))
                               (maybeUnion (C_Exit m) C_Exit))
      ] ++
        case f_maybe of
          Nothing -> []
          Just f -> [entryConstraint f]

    entryConstraint x = C_Entry (annotation x) :=: (C_Entry l)

    maybeUnion x g =
      case f_maybe of
        Nothing -> x
        Just f -> union x (g (annotation f))

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
nop :: () => f NodeId -> ConstraintGen valueC repr ()
nop e =
  tell
    [ C_Exit (annotation e) :=: (C_Entry (annotation e)) ]

connectList :: (Annotated f) => [f NodeId] -> ConstraintGen valueC repr ()
connectList [] = pure ()
connectList [_] = pure ()
connectList (x:y:rest) = do
  connect x y
  connectList (y:rest)

connect :: (Annotated f, Annotated g) => f NodeId -> g NodeId -> ConstraintGen valueC repr ()
connect x y =
  tell
    [ C_Entry (annotation y) :=: (C_Exit (annotation x)) ]

-- | Combine two nodes, to behave as one
sameNode :: (Annotated f, Annotated g) => f NodeId -> g NodeId -> ConstraintGen valueC repr ()
sameNode x y =
  tell
    [ C_Entry (annotation x) :=: (C_Entry (annotation y))
    , C_Exit  (annotation x) :=: (C_Exit  (annotation y))
    ]

-- TODO: Connect to following nodes
handleFunDef :: () => CFunctionDef NodeId -> ConstraintGen valueC repr ()
handleFunDef e@(CFunDef _ _ _ stmt _) = do
  tell
    [ C_Exit (annotation e) :=: SetEmpty
    , C_Entry (annotation stmt) :=: (C_Exit (annotation e))
    ]
  void $ (constAction handleStmt) stmt

handleExtDecl :: () => CExternalDeclaration NodeId -> ConstraintGen valueC repr ()
handleExtDecl (CFDefExt funDef) = handleFunDef funDef
handleExtDecl _ = pure ()

handleTransUnit :: () => (CTranslationUnit NodeId, NodeId) -> ConstraintGen valueC repr ()
handleTransUnit (CTranslUnit xs _, _) = void $ traverse handleExtDecl xs

