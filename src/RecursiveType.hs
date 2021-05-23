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

eval :: Term -> Term
eval (     Index x                  ) = Index x
eval (     Abstraction typ t        ) = Abstraction typ (eval t)
eval (     Application a   b        ) = eval (shift (-1) 0 (subst a (0, shift 1 0 b)))
eval self@(Fix t                    ) = eval (shift (-1) 0 (subst (eval t) (0, shift 1 0 self)))
eval (     Fold   typ  t            ) = Fold typ (eval t)
eval (     Unfold typ1 (Fold typ2 t)) = eval t
eval (     Unfold typ  t            ) = eval (Unfold typ (eval t))

