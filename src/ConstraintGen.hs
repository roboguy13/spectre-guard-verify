{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

module ConstraintGen where

import           Language.C
import           Language.C.Data.Ident

import           Control.Monad.Writer
import           Data.Generics.Uniplate.Data

import           Data.Maybe

import           SetExpr


newtype ConstraintGen a = ConstraintGen (Writer SetConstraints a)
  deriving (Functor, Applicative, Monad, MonadWriter SetConstraints)

execConstraintGen :: ConstraintGen a -> SetConstraints
execConstraintGen (ConstraintGen g) = execWriter g

constActionUncurry :: Applicative f => (a -> b -> f ()) -> (a, b) -> f (a, b)
constActionUncurry f (x, y) = f x y *> pure (x, y)

constAction :: Applicative f => (a -> f ()) -> a -> f a
constAction f x = f x *> pure x

isNoSpecAttr :: Show a => CAttribute a -> Bool
isNoSpecAttr (CAttr (Ident "nospec" _ _) _ _) = True
isNoSpecAttr _ = False

handleDeclarator :: CDeclarator NodeId -> ConstraintGen ()
handleDeclarator e@(CDeclr (Just (Ident ident hash _)) _derivs _strLit attrs n)
  | any isNoSpecAttr attrs = do
      mapM_ (sameNode e) attrs

      tell [c_exit n :=: SE_UnionSingle (c_entry n)
                                  hash (SensAtom Secret)]

  | otherwise = do
      mapM_ (sameNode e) attrs
      tell [c_exit n :=: SE_UnionSingle (c_entry n)
                                  hash (SensAtom Public)]

handleDeclarator e = nop e

handleCompoundItem :: CCompoundBlockItem NodeId -> ConstraintGen ()
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

handleExpr :: CExpression NodeId -> ConstraintGen ()
handleExpr e0@(CAssign _ cv@(CVar (Ident _ x _) _) e n) = do
  let m = annotation e

  e0 `connect` e

  handleExpr cv
  tell [ c_exit n :=: SE_IfThenElse (PairIn (x, Public) (c_entry n))
                                    (SE_UnionSingle (c_entry n) x (Sens_T (annotation e)))
                                    (c_entry n)
       ]
    *> handleExpr e

handleExpr e@(CVar (Ident _ x _) _) =
  tell [ atom_e (annotation e) :=: singleVar x ]

handleExpr expr = do
  nop expr
  let theChildren = children expr

  case theChildren of
    [] -> tell [ atom_e (annotation expr) :=: SE_Empty ]
    (c:cs) ->
      tell [ atom_e (annotation expr) :=: foldr SE_Union (atom_e (annotation c)) (map (atom_e . annotation) cs) ]

  forM_ theChildren $ \c -> do
    -- tell [ c_entry (annotation c) :=: c_exit (annotation expr) ]
    sameNode c expr
    handleExpr c
  -- mapM_ handleExpr $ children expr
  -- go nodeIds
  where
  --   go :: [AtomicSet '[Var]] -> ConstraintGen ()
  --   go [] = pure ()
  --   go [x] = tell [ atom_e exprNodeId :=: SE_Atom x ]-- pure () --tell [ atom_e exprNodeId :=: x ]
  --   go (x:y:rest) = do
  --     tell [atom_e exprNodeId :=: SE_Union x (SE_Atom y)]
  --     go (y:rest)

    exprNodeId = annotation expr

    -- nodeIds = map (atom_e . annotation) . drop 1 $ universe expr

handleStmt :: CStatement NodeId -> ConstraintGen ()
handleStmt e0@(CExpr (Just e) _) = do
  nop e0
  e0 `connect` e
  handleExpr e
handleStmt e0@(CIf cond t f_maybe l) = do
  handleExpr cond

  -- e0 `connect` cond
  tell [ c_entry (annotation cond) :=: c_entry l ]

  tell go

  handleStmt t

  case f_maybe of
    Nothing -> pure ()
    Just f -> handleStmt f
  where
    go =
      [entryConstraint t
      ,c_exit l :=: SE_Union (c_entry l)
                             (SE_IfThenElse (Sens_T l `SensEqual` SensAtom Secret)
                               (maybeUnion (atom_s l m) (atom_s l))
                               (maybeUnion (c_exit m) c_exit))
      ] ++
        case f_maybe of
          Nothing -> []
          Just f -> [entryConstraint f]

    entryConstraint x = c_entry (annotation x) :=: SE_Atom (C_Entry l)

    maybeUnion x g =
      case f_maybe of
        Nothing -> SE_Atom x
        Just f -> SE_Union x (g (annotation f))

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
nop :: Annotated f => f NodeId -> ConstraintGen ()
nop e =
  tell
    [ c_exit (annotation e) :=: c_entry (annotation e) ]

connectList :: Annotated f => [f NodeId] -> ConstraintGen ()
connectList [] = pure ()
connectList [_] = pure ()
connectList (x:y:rest) = do
  connect x y
  connectList (y:rest)

connect :: (Annotated f, Annotated g) => f NodeId -> g NodeId -> ConstraintGen ()
connect x y =
  tell
    [ c_entry (annotation y) :=: c_exit (annotation x) ]

-- | Combine two nodes, to behave as one
sameNode :: (Annotated f, Annotated g) => f NodeId -> g NodeId -> ConstraintGen ()
sameNode x y =
  tell
    [ c_entry (annotation x) :=: c_entry (annotation y)
    , c_exit  (annotation x) :=: c_exit  (annotation y)
    ]

-- TODO: Connect to following nodes
handleFunDef :: CFunctionDef NodeId -> ConstraintGen ()
handleFunDef e@(CFunDef _ _ _ stmt _) = do
  tell
    [ c_exit (annotation e) :=: SE_Empty
    , c_entry (annotation stmt) :=: c_exit (annotation e)
    ]
  void $ (constAction handleStmt) stmt

handleExtDecl :: CExternalDeclaration NodeId -> ConstraintGen ()
handleExtDecl (CFDefExt funDef) = handleFunDef funDef
handleExtDecl _ = pure ()

handleTransUnit :: (CTranslationUnit NodeId, NodeId) -> ConstraintGen ()
handleTransUnit (CTranslUnit xs _, _) = void $ traverse handleExtDecl xs

