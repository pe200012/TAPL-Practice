{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
module GC where

import           Control.Arrow                  ( Arrow(second)
                                                , first
                                                )
import           Control.Monad                  ( ap )
import qualified Data.HashMap.Lazy             as Map
import           Data.Maybe                     ( fromMaybe
                                                , isJust
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
          | Abstraction (String, Type, Term)
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
insertStore x s = (storeCounter s, s { unStore = Map.insert (storeCounter s) x (unStore s), storeCounter = storeCounter s + 1 })

assignStore :: Int -> Term -> Store -> Store
assignStore i t s = s { unStore = Map.insert i t (unStore s) }

deleteStore :: Int -> Store -> Store
deleteStore i s = s { unStore = Map.delete i (unStore s) }

prettyTerm :: Term -> String
prettyTerm (Variable    a          ) = a
prettyTerm (Abstraction (a, typ, t)) = unpack (format "(λ{}:{}. {})" [a, prettyType typ, prettyTerm t])
prettyTerm (Application (a, b)     ) = unpack (format "{} {}" (prettyTerm <$> [a, b]))
prettyTerm Unit                      = "unit"
prettyTerm (Sequential    (a, b) )   = unpack (format "{}; {}" (prettyTerm <$> [a, b]))
prettyTerm (Reference     n      )   = unpack (format "ref {}" [prettyTerm n])
prettyTerm (Dereference   t      )   = unpack (format "!{}" [prettyTerm t])
prettyTerm (Assignment    (t, t'))   = unpack (format "{} := {}" (prettyTerm <$> [t, t']))
prettyTerm (StoreLocation i      )   = unpack (format "[{}]" [i])

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
    go cxt mu (Variable    x          ) = maybe (Left $ unpack $ format "Variable not found: {}" [x]) (return . (, mu)) (lookup x cxt)
    go cxt mu (Abstraction (x, typ, t)) = first (typ :->:) <$> go ((x, typ) : cxt) mu t
    go cxt mu (Application (a, b)     ) = do
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
        return (Ref t', Vector.snoc mu' t')
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
        Just t  -> Right (Ref t, mu)
        Nothing -> Left $ unpack $ format "Invalid reference: {}" [prettyTerm (StoreLocation i)]

fv :: Term -> Set String
fv (Variable    x        ) = singleton x
fv (Abstraction (a, _, b)) = a `delete` fv b
fv (Application (a, b)   ) = fv a `union` fv b
fv Unit                    = empty
fv (Sequential    (a, b))  = fv a `union` fv b
fv (Reference     t     )  = fv t
fv (Dereference   t     )  = fv t
fv (Assignment    (a, b))  = fv a `union` fv b
fv (StoreLocation _     )  = empty

nextAvailableName :: String -> String
nextAvailableName "z" = "aa"
nextAvailableName (splitAt =<< (Prelude.subtract 1 . length) -> (front, Prelude.head -> l)) | l == 'z'  = nextAvailableName front ++ "a"
                                                                                            | otherwise = front ++ [Prelude.succ l]

subst :: Term -> (String, Term) -> Term
subst (Application (a, b)) t = Application (subst a t, subst b t)
subst x@(Abstraction (a, typ, b)) t0@(n, t) | a /= n && a `notMember` fv t = Abstraction (a, typ, subst b t0)
                                            | a `member` fv t = subst (Abstraction (avoidCapture a, typ, subst b (a, Variable (avoidCapture a)))) t0
                                            | otherwise = x
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

-- >>> typecheck (Abstraction ("a", Any, Abstraction ("b", Any, Variable "a")))
-- Right (Any :->: (Any :->: Any))

-- >>> evalCallByName (Application (Abstraction ("x", UnitType, Abstraction ("a", Any, Abstraction ("b", Any, Variable "a"))), Unit))
-- Abstraction ("a",Any,Abstraction ("b",Any,Variable "a"))

-- >>> evalCallByName (Application (Abstraction ("x", Ref UnitType, Unit), Reference Unit))
-- Unit

{-

>>> lam name typ term = Abstraction (name, typ, term)
>>> app = curry Application
>>> tru = Abstraction ("x", Any, Abstraction ("y", Any, Variable "x"))
>>> fls = Abstraction ("x", Any, Abstraction ("y", Any, Variable "y"))
>>> if_ = Abstraction ("b", Any :->: (Any :->: Any), Abstraction ("x", Any, Abstraction ("y", Any, Application (Application (Variable "b", Variable "x"), Variable "y"))))
>>> zero = fls
>>> succ_ = lam "n" (Any :->: (Any :->: Any)) (lam "s" (Any :->: Any) (lam "z" (Any :->: (Any :->: Any)) (app (Variable "s") (app (app (Variable "n") (Variable "s")) (Variable "z")))))
>>> one = lam "s" (Any :->: Any) (lam "z" Any (app (Variable "s") (Variable "z")))

>>> typecheck <$> [tru,fls,if_]
[Right (Any :->: (Any :->: Any)),Right (Any :->: (Any :->: Any)),Right ((Any :->: (Any :->: Any)) :->: (Any :->: (Any :->: Any)))]

>>> typecheck zero
Right (Any :->: (Any :->: Any))

>>> typecheck (Application (succ_, zero))
Right ((Any :->: Any) :->: ((Any :->: (Any :->: Any)) :->: Any))

>>> typecheck (Reference tru)
Right (Ref (Any :->: (Any :->: Any)))

>>> evalCallByName (Application (Abstraction ("x", Ref (Any :->: (Any :->: Any)), Application (Application (Dereference (Variable "x"), zero), one)), Reference fls))
Abstraction ("x",Any,Abstraction ("y",Any,Variable "y"))

>>> evalCallByName (app (lam "x" (Ref UnitType) (Dereference (Variable "x"))) (Reference Unit))
Unit

>>> evalCallByName (app (lam "x" (Ref (Any :->: Any)) (app (Dereference (Variable "x")) one)) (Reference tru))
Abstraction ("x",Any,Abstraction ("y",Any,Variable "x"))


-}
evalCallByName :: Term -> Term
evalCallByName = either error . const . eval emptyStore <*> typecheck
  where
    eval = ap (`maybe` uncurry eval) . go
    go :: Store -> Term -> Maybe (Store, Term)
    go store (Variable    _     ) = Nothing
    go store (Application (a, b)) = case typecheck b of
        Right (Ref _) -> Just (maybe app' (second (Application . (a, ))) (go store b))
        _             -> Just app'
      where
        app' = flip fromMaybe (go store a) $ case a of
            Abstraction (x, _, y) -> (store, subst y (x, b))
            _                     -> error "eval: impossible to reach here(app)"
    go store (Abstraction (a, _, b)) = Nothing
    go store Unit                    = Nothing
    go store (Sequential  (a, b))    = Just (maybe (store, b) (second (Sequential . (, b))) (go store a))
    go store (Reference   t     )    = let (i, store') = insertStore t store in Just (store', StoreLocation i)
    go store (Dereference i     )    = maybe deref (return . second Dereference) (go store i)
      where
        deref = case i of
            StoreLocation index -> Just (maybe (error "eval: Reference not found") (store, ) (lookupStore index store))
            _                   -> error "eval: impossible to reach here(defer)"
    go store (Assignment (a, b)) = do
        (s', a') <- go store a
        case a' of
            StoreLocation i -> Just (assignStore i b store, Unit)
            _               -> error "eval: impossible to reach here(assign)"
    go store (StoreLocation i) = Nothing
