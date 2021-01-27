{-# LANGUAGE DeriveAnyClass #-}
module Main where

import Prelude hiding (succ, pred)

newtype Simple = Simple [Term]

data Term = Boolean Bool
          | NAT Nat
          | IF Term Term Term
          deriving Show

data Nat = Zero
         | Succ Nat
         deriving (Show, Eq)

{-|

>>> isZero Zero
Boolean True

>>> isZero (Succ Zero)
Boolean False

-}
isZero :: Nat -> Term
isZero Zero = Boolean True
isZero _    = Boolean False

{-|

>>> isZero (pred (succ Zero))
Boolean True

-}
succ :: Nat -> Nat
succ = Succ

pred :: Nat -> Nat
pred Zero     = error "Zero"
pred (Succ n) = n

main :: IO ()
main = pure ()
