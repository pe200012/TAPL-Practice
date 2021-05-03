{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module GC where

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

-- | copying original untyped λ-calculus with reference extension
data Term = Variable String
          | Abstraction (String, Term)
          | Application (Term, Term)
          | Unit
          | Term :>: Term
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

prettyTerm :: Term -> String
prettyTerm (Variable    a     ) = a
prettyTerm (Abstraction (a, t)) = unpack (format "(λ{}. {})" [a, prettyTerm t])
prettyTerm (Application (a, b)) = unpack (format "{} {}" (prettyTerm <$> [a, b]))
prettyTerm Unit                 = "unit"
prettyTerm (a :>: b)            = unpack (format "{}; {}" (prettyTerm <$> [a, b]))

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

typecheck :: Term -> Either String Type
typecheck = go []
  where
    go cxt (Variable    x     ) = maybe (Left $ unpack $ format "Variable not found: {}" [x]) return (lookup x cxt)
    go cxt (Abstraction (x, t)) = case analyseUsage x t of
        NotMentioned -> do
            t' <- go cxt t
            return (Any :->: t')
        LooksLike a -> do
            t' <- go ((x, a) : cxt) t
            return (a :->: t')
        Inconsistent   (a, b) -> Left $ unpack $ format "Type inconsistency: first {}, later {}" (prettyType <$> [a, b])
        TypecheckError s      -> Left s
      where
        analyseUsage x (Variable n) | x == n    = LooksLike Any
                                    | otherwise = NotMentioned
        analyseUsage x (Abstraction (n, t)) | x == n    = NotMentioned
                                            | otherwise = analyseUsage x t
        analyseUsage x (Application (a, b)) = case analyseUsage x a of
            NotMentioned -> analyseUsage x b
            LooksLike Any ->
                either TypecheckError (\t' -> either TypecheckError (LooksLike . (:->: Any)) (go ((x, t' :->: Any) : cxt) b)) (go ((x, Any) : cxt) b)
            LooksLike      t      -> either TypecheckError (\t' -> if t `typeNotEqual` t' then Inconsistent (t, t') else LooksLike t) (go ((x, Any) : cxt) b)
            Inconsistent   (a, b) -> Inconsistent (a, b)
            TypecheckError s      -> TypecheckError s
        analyseUsage x Unit      = NotMentioned
        analyseUsage x (a :>: b) = case (analyseUsage x a, analyseUsage x b) of
            (LooksLike Any, t            ) -> t
            (t            , LooksLike Any) -> t
            (LooksLike a  , LooksLike b  ) -> maybe (Inconsistent (a, b)) LooksLike (typeRefine a b)
            (x            , _            ) -> x
    go cxt (Application (a, b)) = do
        a' <- go cxt a
        b' <- go cxt b
        case a' of
            t :->: s | t `typeEqual` b' -> Right s
                     | otherwise        -> Left $ unpack $ format "Type mismatch: expected {}, but was given {}" (prettyType <$> [t, b'])
            _ -> Left $ unpack $ format "Type mismatch: expected {}, but was given {}" (prettyType <$> [b' :->: Any, a'])
    go cxt Unit      = Right UnitType
    go cxt (a :>: b) = do
        t <- go cxt a
        case t of
            UnitType -> go cxt b
            _        -> Left $ unpack $ format "Type mismatch: expected {}, but was given {}" (prettyType <$> [UnitType, t])

fv :: Term -> Set String
fv (Variable    x     ) = singleton x
fv (Abstraction (a, b)) = a `delete` fv b
fv (Application (a, b)) = fv a `union` fv b
fv Unit                 = empty
fv (a :>: b)            = fv a `union` fv b

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
subst Unit      _ = Unit
subst (a :>: b) p = subst a p :>: subst b p

evalCallByName :: Term -> Term
evalCallByName = flip maybe evalCallByName <*> go
  where
    go (Variable    _     ) = Nothing
    go (Application (a, b)) = case a of
        Abstraction (x, y) -> Just (subst y (x, b))
        x                  -> do
            a' <- go a
            return (Application (a', b))
    go (Abstraction (a, b)) = Nothing
    go Unit                 = Nothing
    go (a :>: b)            = do
        a' <- go a
        case a' of
            Unit -> Just b
            _    -> Nothing
