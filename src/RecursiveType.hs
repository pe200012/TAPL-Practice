{-# LANGUAGE OverloadedStrings #-}
module RecursiveType where

import           Data.Text.Format               ( format )
import           Data.Text.Lazy                 ( unpack )

data Term = Index Int
          | Abstraction Type Term
          | Application Term Term
          | Fix Term
          | Fold Type Term
          | Unfold Type Term
           deriving Show

data Type = Type :-> Type
          | TypeVariable Int
          | Mu Type
          | Unfolding (Type, [Type])
    deriving (Show, Eq)

prettyTerm :: Term -> String
prettyTerm (Index i          ) = show i
prettyTerm (Abstraction typ t) = unpack (format "(λ{}. {})" [show typ, prettyTerm t])
prettyTerm (Application a   b) = unpack (format "{} {}" (prettyTerm <$> [a, b]))
prettyTerm (Fix t            ) = unpack (format "fixpoint ({})" [prettyTerm t])
prettyTerm (Fold   typ t     ) = unpack (format "fold [{}] ({})" [show typ, prettyTerm t])
prettyTerm (Unfold typ t     ) = unpack (format "unfold [{}] ({})" [show typ, prettyTerm t])

shift :: Int -> Int -> Term -> Term
shift distance cutoff (Index i          ) = Index (if i < cutoff then i else i + distance)
shift distance cutoff (Abstraction typ t) = Abstraction typ (shift distance (succ cutoff) t)
shift distance cutoff (Application a   b) = Application (shift distance cutoff a) (shift distance cutoff b)
shift distance cutoff (Fix t            ) = Fix (shift distance cutoff t)
shift distance cutoff (Fold   typ t     ) = Fold typ (shift distance cutoff t)
shift distance cutoff (Unfold typ t     ) = Unfold typ (shift distance cutoff t)

subst :: Term -> (Int, Term) -> Term
subst (Index k) (j, s) | k == j    = s
                       | otherwise = Index k
subst (Abstraction typ t1) (j, s) = Abstraction typ (subst t1 (succ j, shift 1 0 s))
subst (Application t1  t2) p      = Application (subst t1 p) (subst t2 p)
subst (Fix t             ) p      = Fix (subst t p)
subst (Fold   typ t      ) p      = Fold typ (subst t p)
subst (Unfold typ t      ) p      = Unfold typ (subst t p)

typeshift :: Int -> Int -> Type -> Type
typeshift distance cutoff (a :-> b                   ) = typeshift distance cutoff a :-> typeshift distance cutoff b
typeshift distance cutoff (TypeVariable i            ) = TypeVariable (if i < cutoff then i else i + distance)
typeshift distance cutoff (Mu           t            ) = Mu (typeshift distance (succ cutoff) t)
typeshift distance cutoff (Unfolding    (typ, []    )) = Unfolding (typeshift distance cutoff typ, [])
typeshift distance cutoff (Unfolding    (typ, x : xs)) = typeshift distance cutoff (Unfolding (typesubst typ (0, x), xs))

typesubst :: Type -> (Int, Type) -> Type
typesubst (a :-> b) p = typesubst a p :-> typesubst b p
typesubst (TypeVariable i) (j, k) | i == j    = k
                                  | otherwise = TypeVariable i
typesubst (Mu        t            ) (i, j) = Mu (typesubst t (succ i, typeshift 1 0 j))
typesubst (Unfolding (typ, []    )) p      = Unfolding (typesubst typ p, [])
typesubst (Unfolding (typ, x : xs)) p      = typesubst (Unfolding (typesubst typ (0, x), xs)) p

typesubst' :: Type -> Type -> Type
typesubst' t u = typeshift (-1) 0 (typesubst (typeshift 1 0 t) (0, u))

-- >>> typing (Fold (Mu (Mu (TypeVariable 1))) (Unfold (Mu (Mu (TypeVariable 1))) (Fold (Mu (Mu (TypeVariable 1))) (Fix (Abstraction (Mu (TypeVariable 0)) (Index 0))))))
-- Right (Mu (Mu (TypeVariable 0)))

typing :: Term -> Either String Type
typing = go [] []
  where
    go vars typecxt (Index i) | i >= length vars = Left (unpack $ format "typing: variable not found (Index {})" [show i])
                              | otherwise        = Right (vars !! i)
    go vars typecxt (Abstraction typ t) = (typ :->) <$> go (typ : vars) typecxt t
    go vars typecxt (Application a   b) = do
        a' <- go vars typecxt a
        b' <- go vars typecxt b
        case a' of
            t :-> u | t == b'   -> Right u
                    | otherwise -> Left (unpack $ format "typing: type mismatch. Expected {}, got {}" [show t, show b'])
            _ -> Left (unpack $ format "typing: type mismatch. Expected arrow type, got {}" [show a'])
    go vars typecxt (Fix t) = do
        t' <- go vars typecxt t
        case t' of
            (a :-> b) | a == b    -> Right b
                      | otherwise -> Left (unpack $ format "typing: type mismatch. Expected {}, got {}" [show a, show b])
            _ -> Left (unpack $ format "typing: type mismatch. Expected arrow type, got {}" [show t'])
    go vars typecxt (Fold typ t) = do
        typ' <- go vars typecxt t
        case typ' of
            Unfolding (u, []) -> Right (Mu u)
            Unfolding (u, [x]) | typ == x  -> Right (Mu u)
                               | otherwise -> err typ x
            Unfolding (u, x : xs) | typ == x  -> Right (Unfolding (Mu u, xs))
                                  | otherwise -> err typ x
            u -> Right (Mu u)
        where err typ x = Left (unpack $ format "typing: type mismatch. Expected {}, got {}" [show typ, show x])
    go vars typecxt (Unfold typ t) = do
        typ' <- go vars typecxt t
        case typ' of
            Mu        u            -> Right (Unfolding (u, [typ]))
            Unfolding (Mu u, typs) -> Right (Unfolding (u, typ : typs))
            _                      -> Left (unpack $ format "typing(unfold): type mismatch. Expected recursive type, got {}" [show typ'])

eval :: Term -> Term
eval (     Index x                  ) = Index x
eval (     Abstraction typ t        ) = Abstraction typ (eval t)
eval (     Application a   b        ) = eval (shift (-1) 0 (subst a (0, shift 1 0 b)))
eval self@(Fix t                    ) = eval (shift (-1) 0 (subst (eval t) (0, shift 1 0 self)))
eval (     Fold   typ  t            ) = Fold typ (eval t)
eval (     Unfold typ1 (Fold typ2 t)) = eval t
eval (     Unfold typ  t            ) = eval (Unfold typ (eval t))

eval' :: Term -> Term
eval' = either error . const . eval <*> typing
