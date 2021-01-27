{-# LANGUAGE DeriveAnyClass #-}
module Main where

import Prelude hiding (succ, pred)
import Data.Set

newtype Simple = Simple [Term]

data Term = TTrue
          | TFalse
          | Zero
          | Succ Term
          | Pred Term
          | IsZero Term
          | IF Term Term Term
          deriving (Show, Eq, Ord)

{-|

>>> isZero Zero
TTrue

>>> isZero (Succ Zero)
TFalse

-}
isZero :: Term -> Term
isZero Zero = TTrue
isZero _    = TFalse

{-|

>>> isZero (pred (succ Zero))
TTrue

-}
succ :: Term -> Term
succ = Succ

pred :: Term -> Term
pred Zero     = error "Zero"
pred (Succ n) = n

consts :: Term -> Set Term
consts Zero       = singleton Zero
consts (Succ n)   = consts n
consts (Pred n)   = consts n
consts TTrue      = singleton TTrue
consts TFalse     = singleton TFalse
consts (IsZero n) = consts n
consts (IF a b c) = consts a `union` consts b `union` consts c

tSize :: Term -> Int
tSize TTrue  = 1
tSize TFalse = 1
tSize Zero   = 1
tSize (Succ n) = tSize n + 1
tSize (Pred n) = tSize n + 1
tSize (IsZero n) = tSize n + 1
tSize (IF a b c) = sum (tSize <$> [a,b,c]) + 1

depth :: Term -> Int
depth TTrue  = 1
depth TFalse = 1
depth Zero   = 1
depth (Succ n) = depth n + 1
depth (Pred n) = depth n + 1
depth (IsZero n) = depth n + 1
depth (IF a b c) = maximum (depth <$> [a,b,c]) + 1


main :: IO ()
main = pure ()
