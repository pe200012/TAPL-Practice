{-# LANGUAGE OverloadedStrings #-}
module Subtyping where

import           Data.Text.Format               ( format )
import           Data.Text.Lazy                 ( Text
                                                , unpack
                                                )
import           Data.Void                      ( Void )
import           Text.Megaparsec                ( (<|>)
                                                , MonadParsec(try)
                                                , Parsec
                                                , choice
                                                , many
                                                , optional
                                                )
import           Text.Megaparsec.Char           ( char
                                                , digitChar
                                                , space
                                                )

newtype Nat = Nat { unNat :: Int } deriving (Show, Eq)

instance Num Nat where
    Nat a + Nat b = Nat (a + b)
    Nat a * Nat b = Nat (a * b)
    abs    = id
    signum = const 1
    fromInteger x | x < 0     = error "Nat should be positive"
                  | otherwise = Nat (fromIntegral x)
    negate = error "undefined negate on Nat"

data Term = Index Int
          | Abstraction Type Term
          | Application Term Term
          | NaturalNumber Nat
    deriving Show

data Type = Type :-> Type
          | NatNumber
    deriving (Show, Eq)

prettyTerm :: Term -> String
prettyTerm (Index i          ) = show i
prettyTerm (Abstraction typ t) = unpack (format "(λ{}. {})" [show typ, prettyTerm t])
prettyTerm (Application a   b) = unpack (format "{} {}" (prettyTerm <$> [a, b]))
prettyTerm (NaturalNumber i  ) = show i

shift :: Int -> Int -> Term -> Term
shift distance cutoff (  Index i          ) = Index (if i < cutoff then i else i + distance)
shift distance cutoff (  Abstraction typ t) = Abstraction typ (shift distance (succ cutoff) t)
shift distance cutoff (  Application a   b) = Application (shift distance cutoff a) (shift distance cutoff b)
shift distance cutoff t@(NaturalNumber _  ) = t

subst :: Term -> (Int, Term) -> Term
subst (Index k) (j, s) | k == j    = s
                       | otherwise = Index k
subst (  Abstraction typ t1) (j, s) = Abstraction typ (subst t1 (succ j, shift 1 0 s))
subst (  Application t1  t2) p      = Application (subst t1 p) (subst t2 p)
subst t@(NaturalNumber _   ) p      = t

typeshift :: Int -> Int -> Type -> Type
typeshift distance cutoff (a :-> b) = typeshift distance cutoff a :-> typeshift distance cutoff b
typeshift distance cutoff NatNumber = NatNumber

typesubst :: Type -> (Int, Type) -> Type
typesubst (a :-> b) p = typesubst a p :-> typesubst b p
typesubst NatNumber p = NatNumber

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
    go vars typecxt (NaturalNumber _) = return NatNumber

eval :: Term -> Term
eval (Index x          ) = Index x
eval (Abstraction typ t) = Abstraction typ (eval t)
eval (Application a   b) = eval (shift (-1) 0 (subst a (0, shift 1 0 b)))
eval (NaturalNumber i  ) = NaturalNumber i

eval' :: Term -> Term
eval' = either error . const . eval <*> typing
