{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
module GC where

import qualified Data.HashMap.Lazy             as Map
import           Data.Maybe                     ( isJust
                                                , isNothing
                                                )
import           Data.Set                       ( Set
                                                , delete
                                                , empty
                                                , member
                                                , notMember
                                                , singleton
                                                , union
                                                )
import           Data.Text.Format               ( format )
import           Data.Text.Lazy                 ( unpack )
import           Data.Vector                    ( Vector )
import qualified Data.Vector                   as Vector

-- | copying original untyped λ-calculus with reference extension
data Term = Variable String
          | Abstraction (String, Term)
          | Application (Term, Term)
          | Unit
          | Sequential (Term, Term)
          | Reference Term
          | Dereference Term
          | Assignment (Term, Term)
          | StoreLocation Int
           deriving Show

data Type = Type :->: Type
          | UnitType
          | Ref Type
          | Any
          deriving (Show, Eq)

data Usage = NotMentioned
           | LooksLike Type
           | Inconsistent (Type, Type)
           | TypecheckError String

data Store = Store
    { unStore      :: Map.HashMap Int Term
    , storeCounter :: Int
    }
    deriving Show

emptyStore :: Store
emptyStore = Store Map.empty 0

lookupStore :: Int -> Store -> Maybe Term
lookupStore i = Map.lookup i . unStore

insertStore :: Term -> Store -> (Int, Store)
insertStore x s = (storeCounter s + 1, s { unStore = Map.insert (storeCounter s) x (unStore s) })

deleteStore :: Int -> Store -> Store
deleteStore i s = s { unStore = Map.delete i (unStore s) }

prettyTerm :: Term -> String
prettyTerm (Variable    a     )    = a
prettyTerm (Abstraction (a, t))    = unpack (format "(λ{}. {})" [a, prettyTerm t])
prettyTerm (Application (a, b))    = unpack (format "{} {}" (prettyTerm <$> [a, b]))
prettyTerm Unit                    = "unit"
prettyTerm (Sequential    (a, b) ) = unpack (format "{}; {}" (prettyTerm <$> [a, b]))
prettyTerm (Reference     n      ) = unpack (format "ref {}" [prettyTerm n])
prettyTerm (Dereference   t      ) = unpack (format "!{}" [prettyTerm t])
prettyTerm (Assignment    (t, t')) = unpack (format "{} := {}" (prettyTerm <$> [t, t']))
prettyTerm (StoreLocation i      ) = unpack (format "[{}]" [i])

prettyType :: Type -> String
prettyType (a :->: b) = unpack $ format "({} -> {})" (prettyType <$> [a, b])
prettyType UnitType   = "Unit"
prettyType (Ref t)    = unpack $ format "Ref {}" [prettyType t]
prettyType Any        = "Any"

typeRefine :: Type -> Type -> Maybe Type
typeRefine Any        x          = Just x
typeRefine x          Any        = Just x
typeRefine (a :->: b) (c :->: d) = (:->:) <$> typeRefine a c <*> typeRefine b d
typeRefine (Ref a   ) (Ref b   ) = Ref <$> typeRefine a b
typeRefine UnitType   UnitType   = Just UnitType
typeRefine _          _          = Nothing

typeEqual :: Type -> Type -> Bool
typeEqual = (.) isJust . typeRefine

typeNotEqual :: Type -> Type -> Bool
typeNotEqual = (.) isNothing . typeRefine

(-$) :: (a -> b -> c) -> b -> a -> c
(-$) = flip

{-

>>> helper = fmap prettyType . typecheck

>>> helper (Variable "abc")
Left "Variable not found: abc"

>>> helper (Abstraction ("x", Variable "x"))
Right "(Any -> Any)"

>>> helper (Abstraction ("x", Unit))
Right "(Any -> Unit)"

>>> helper (Application (Abstraction ("x", Variable "x"), Unit))
Right "Any"
-- wtf

-}

typecheck :: Term -> Either String Type
typecheck = fmap fst . go [] Vector.empty
  where
    go :: [(String, Type)] -> Vector Type -> Term -> Either String (Type, Vector Type)
    go cxt mu (Variable    x     ) = maybe (Left $ unpack $ format "Variable not found: {}" [x]) (return . (, mu)) (lookup x cxt)
    go cxt mu (Abstraction (x, t)) = case analyseUsage x t of
        NotMentioned -> do
            (t', mu') <- go cxt mu t
            return (Any :->: t', mu')
        LooksLike a -> do
            (t', mu') <- go ((x, a) : cxt) mu t
            return (a :->: t', mu')
        Inconsistent   (a, b) -> Left $ unpack $ format "Type inconsistency: first {}, later {}" (prettyType <$> [a, b])
        TypecheckError s      -> Left s
      where
        analyseUsage x (Variable n) | x == n    = LooksLike Any
                                    | otherwise = NotMentioned
        analyseUsage x (Abstraction (n, t)) | x == n    = NotMentioned
                                            | otherwise = analyseUsage x t
        analyseUsage x (Application (a, b)) = case analyseUsage x a of
            NotMentioned  -> analyseUsage x b
            LooksLike Any -> either TypecheckError
                                    (\(t', mu) -> either TypecheckError (LooksLike . (:->: Any) . fst) (go ((x, t' :->: Any) : cxt) mu b))
                                    (go ((x, Any) : cxt) mu b)
            LooksLike t -> either TypecheckError (\(t', _) -> if t `typeNotEqual` t' then Inconsistent (t, t') else LooksLike t) (go ((x, Any) : cxt) mu b)
            Inconsistent (a, b) -> Inconsistent (a, b)
            TypecheckError s -> TypecheckError s
        analyseUsage x Unit                = NotMentioned
        analyseUsage x (Sequential (a, b)) = case analyseUsage x a of
            NotMentioned -> analyseUsage x b
            LooksLike t  -> case analyseUsage x b of
                NotMentioned -> LooksLike t
                LooksLike t' -> maybe (Inconsistent (t, t')) LooksLike (typeRefine t t')
                e            -> e
            e -> e
        analyseUsage x (Reference   t) = analyseUsage x t
        analyseUsage x (Dereference t) = case analyseUsage x t of
            LooksLike t' | finallyUsed x t -> LooksLike (Ref t')
                         | otherwise       -> LooksLike t'
            e -> e
        analyseUsage x (Assignment (a, b)) = case analyseUsage x a of
            NotMentioned -> analyseUsage x b
            LooksLike t | finallyUsed x a -> testB (Ref t)
                        | otherwise       -> testB t
            e -> e
          where
            testB t' = case analyseUsage x b of
                NotMentioned  -> LooksLike t'
                LooksLike t'' -> maybe (Inconsistent (t', t'')) LooksLike (typeRefine t' t'')
                e             -> e
        analyseUsage x (StoreLocation i) = NotMentioned
        finallyUsed x (Variable n)           = x == n
        finallyUsed x (Abstraction (n, t))   = x /= n && finallyUsed x t
        finallyUsed x (Application (Abstraction (n, t), b)) = finallyUsed x t || (finallyUsed x b && finallyUsed n t)
        finallyUsed x (Application _)        = False
        finallyUsed x Unit                   = False
        finallyUsed x (Sequential    (_, t)) = finallyUsed x t
        finallyUsed x (Reference     t     ) = finallyUsed x t
        finallyUsed x (Dereference   t     ) = finallyUsed x t
        finallyUsed x (Assignment    _     ) = False
        finallyUsed x (StoreLocation _     ) = False

    go cxt mu (Application (a, b)) = do
        (a', mu' ) <- go cxt mu a
        (b', mu'') <- go cxt mu' b
        case a' of
            t :->: s | t `typeEqual` b' -> Right (s, mu'')
                     | otherwise        -> Left $ unpack $ format "Type mismatch: expected {}, but was given {}" (prettyType <$> [t, b'])
            _ -> Left $ unpack $ format "Type mismatch: expected {}, but was given {}" (prettyType <$> [b' :->: Any, a'])
    go cxt mu Unit                = Right (UnitType, mu)
    go cxt mu (Sequential (a, b)) = do
        (a', _) <- go cxt mu a
        case a' of
            UnitType -> go cxt mu b
            _        -> Left $ unpack $ format "Type mismatch: expected Unit, but was given {}" [prettyType a']
    go cxt mu (Reference t) = do
        (t', mu') <- go cxt mu t
        return (t', Vector.snoc mu' t')
    go cxt mu (Dereference t) = do
        (t', mu') <- go cxt mu t
        case t' of
            Ref t'' -> Right (t'', mu)
            _       -> Left $ unpack $ format "Type mismatch: expected Ref type, but was given {}" [prettyType t']
    go cxt mu (Assignment (a, b)) = do
        (a', mu' ) <- go cxt mu a
        (b', mu'') <- go cxt mu' b
        case a' of
            Ref t ->
                maybe (Left $ unpack $ format "Type mismatch: expected {}, but was given {}" (prettyType <$> [t, b'])) (return . (, mu'')) (typeRefine t b')
            _ -> Left $ unpack $ format "Type mismatch: expected Ref type, but was given {}" [prettyType a']
    go cxt mu (StoreLocation i) = case mu Vector.!? i of
        Just t  -> Right (t, mu)
        Nothing -> Left $ unpack $ format "Invalid reference: {}" [prettyTerm (StoreLocation i)]

fv :: Term -> Set String
fv (Variable    x     )   = singleton x
fv (Abstraction (a, b))   = a `delete` fv b
fv (Application (a, b))   = fv a `union` fv b
fv Unit                   = empty
fv (Sequential    (a, b)) = fv a `union` fv b
fv (Reference     t     ) = fv t
fv (Dereference   t     ) = fv t
fv (Assignment    (a, b)) = fv a `union` fv b
fv (StoreLocation _     ) = empty

nextAvailableName :: String -> String
nextAvailableName "z" = "aa"
nextAvailableName (splitAt =<< (Prelude.subtract 1 . length) -> (front, Prelude.head -> l)) | l == 'z'  = nextAvailableName front ++ "a"
                                                                                            | otherwise = front ++ [Prelude.succ l]

subst :: Term -> (String, Term) -> Term
subst (Application (a, b)) t = Application (subst a t, subst b t)
subst x@(Abstraction (a, b)) t0@(n, t) | a /= n && a `notMember` fv t = Abstraction (a, subst b t0)
                                       | a `member` fv t              = subst (Abstraction (avoidCapture a, subst b (a, Variable (avoidCapture a)))) t0
                                       | otherwise                    = x
  where
    avoidCapture n | n `member` (fv b `union` fv t) = avoidCapture (nextAvailableName n)
                   | otherwise                      = n
subst x@(Variable a) (b, t) | a /= b    = x
                            | otherwise = t
subst Unit                     _  = Unit
subst (  Sequential    (a, b)) t  = Sequential (subst a t, subst b t)
subst (  Reference     t     ) t' = Reference (subst t t')
subst (  Dereference   t     ) t' = Dereference (subst t t')
subst (  Assignment    (a, b)) t  = Assignment (subst a t, subst b t)
subst x@(StoreLocation _     ) _  = x

-- >>> evalCallByName (Application (Abstraction ("x", Abstraction ("a", Abstraction ("b", Variable "a"))), Unit))
-- Abstraction ("a",Abstraction ("b",Variable "a"))

evalCallByName :: Term -> Term
evalCallByName = either error . const . eval <*> typecheck
  where
    eval = flip maybe eval <*> go
    go (Variable    _     ) = Nothing
    go (Application (a, b)) = case a of
        Abstraction (x, y) -> Just (subst y (x, b))
        x                  -> do
            a' <- go a
            return (Application (a', b))
    go (Abstraction (a, b)) = Nothing
    go Unit                 = Nothing
