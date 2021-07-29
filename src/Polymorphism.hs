{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
module Polymorphism where

import           Control.Lens                   ( over
                                                , view
                                                )
import           Control.Lens.TH
import           Control.Monad                  ( unless )
import           Control.Monad.Except           ( ExceptT
                                                , MonadError(throwError)
                                                , runExceptT
                                                )
import           Control.Monad.State.Lazy       ( MonadState
                                                , State
                                                , gets
                                                , modify
                                                , runState
                                                )
import           Data.Set                       ( Set
                                                , empty
                                                , insert
                                                , singleton
                                                , union
                                                )

-- | Simply typed lambda-calculus with booleans and numbers.
data Term = Lam Type Term
          | Var Int
          | App Term Term
          | Zro
          | Suc Term
          | Boolean Bool
          | IF Term Term Term
          deriving (Show, Eq)

-- | Types with variables
data Type = Bool
          | Nat
          | Type :-> Type
          | TypeVariable Int
          deriving (Show, Eq, Ord)

newtype Constraint = Constraint (Type, Type)
    deriving (Show)

instance Eq Constraint where
    (Constraint (a, b)) == (Constraint (c, d)) = ((a == c) && (b == d)) || ((a == d) && (b == c))

instance Ord Constraint where
    compare a@(Constraint (a1, a2)) b@(Constraint (b1, b2)) | a == b    = EQ
                                                            | otherwise = compare (a1, a2) (b1, b2)

newtype Typing = Typing (Int, Type)
    deriving (Show, Eq)

type TypeContext = [Typing]

substitute :: (Int, Type) -> Type -> Type
substitute (x, p) (a :-> b) = substitute (x, p) a :-> substitute (x, p) b
substitute (x, p) Bool      = Bool
substitute (x, p) Nat       = Nat
substitute (x, p) (TypeVariable y) | y == x    = p
                                   | otherwise = TypeVariable y

class FreeVariable a where
    fv :: a -> Set Int

instance FreeVariable Type where
    fv (a :-> b       ) = fv a `union` fv b
    fv (TypeVariable x) = singleton x
    fv _                = empty

instance FreeVariable Term where
    fv = go 0
      where
        go i (Var x) | x >= i    = singleton x
                     | otherwise = empty
        go i (Lam _ x ) = go (succ i) x
        go i (App x y ) = go i x `union` go i y
        go i (Suc x   ) = go i x
        go i (IF x y z) = go i x `union` go i y `union` go i z
        go _ _          = empty

-- \x:S -> Suc x => S = Nat
-- \x:S -> \y:T -> Suc (x y) ==> S = T -> Nat

{-

>>> typeof' xs t = runState (runExceptT (typeof xs t)) (TypeCheckContext empty 0)

>>> typeof' [] Zro
(Right Nat,TypeCheckContext {_constraints = fromList [], _nextTV = 0})

>>> typeof' [] (Suc Zro)
(Right Nat,TypeCheckContext {_constraints = fromList [], _nextTV = 0})

>>> typeof' [] (Boolean True)
(Right Bool,TypeCheckContext {_constraints = fromList [], _nextTV = 0})

>>> typeof' [] (Var 0)
(Right (TypeVariable 0),TypeCheckContext {_constraints = fromList [], _nextTV = 1})

>>> typeof' [] (Lam Nat (Var 0))
(Right (Nat :-> Nat),TypeCheckContext {_constraints = fromList [], _nextTV = 0})

>>> typeof' [] (App (Lam Nat (Suc (Var 0))) Zro)
(Right Nat,TypeCheckContext {_constraints = fromList [], _nextTV = 0})

>>> typeof' [] (App (Lam Nat (Suc (Var 0))) (Boolean False))
(Left (Mismatch Nat Bool),TypeCheckContext {_constraints = fromList [], _nextTV = 0})

>>> typeof' [] (App (Lam (TypeVariable 0) (Suc (Var 0))) Zro)
(Right Nat,TypeCheckContext {_constraints = fromList [Constraint (TypeVariable 0,Nat)], _nextTV = 0})

>>> typeof' [] (App (Lam (TypeVariable 0) (Suc (Var 0))) (Var 0))
(Right Nat,TypeCheckContext {_constraints = fromList [Constraint (TypeVariable 0,Nat),Constraint (TypeVariable 0,TypeVariable 0)], _nextTV = 1})

>>> typeof' [] (App (App (Lam (TypeVariable 0) (Suc (Var 0))) (Var 0)) (Var 0))
(Left (UnexpectedType Nat),TypeCheckContext {_constraints = fromList [Constraint (TypeVariable 0,Nat),Constraint (TypeVariable 0,TypeVariable 1)], _nextTV = 2})

>>> typeof' [] (Lam (TypeVariable 0) (Suc (Var 0)))
(Right (TypeVariable 0 :-> Nat),TypeCheckContext {_constraints = fromList [Constraint (TypeVariable 0,Nat)], _nextTV = 0})

>>> typeof' [] (App (Lam (TypeVariable 0) (IF (Var 0) Zro (Suc Zro))) (Var 0))
(Right Nat,TypeCheckContext {_constraints = fromList [Constraint (TypeVariable 0,Bool),Constraint (TypeVariable 0,TypeVariable 0)], _nextTV = 1})

>>> typeof' [] (Lam (TypeVariable 0) (IF Zro Zro (Var 0)))
(Left (Mismatch Nat Bool),TypeCheckContext {_constraints = fromList [], _nextTV = 0})

-}

data TypeCheckContext = TypeCheckContext
    { _constraints :: Set Constraint
    , _nextTV      :: Int
    }
    deriving Show

makeLenses ''TypeCheckContext

data TypeError = Mismatch Type Type
               | UnexpectedType Type
               deriving (Show)

fetchTV :: MonadState TypeCheckContext m => m Int
fetchTV = do
    tv <- gets (view nextTV)
    modify (over nextTV succ)
    return tv

typeof :: [Type] -> Term -> ExceptT TypeError (State TypeCheckContext) Type
typeof types (Lam ty te) = (ty :->) <$> typeof (ty : types) te
typeof types (Var n) | n < length types = return (types !! n)
                     | otherwise        = TypeVariable <$> fetchTV
typeof types (App te te') = do
    t2 <- typeof types te'
    t1 <- typeof types te
    case t1 of
        Bool       -> throwError $ UnexpectedType Bool
        Nat        -> throwError $ UnexpectedType Nat
        ty :-> ty' -> if null (fv t1) && null (fv t2)
            then (if ty /= t2 then throwError $ Mismatch ty t2 else return ty')
            else do
                modify (over constraints (insert (Constraint (ty, t2))))
                return ty'
        TypeVariable n -> do
            modify (over constraints (insert (Constraint (t1, t2))))
            TypeVariable <$> fetchTV
typeof types Zro      = return Nat
typeof types (Suc te) = do
    t <- typeof types te
    unless (null (fv t)) (modify (over constraints (insert (Constraint (t, Nat)))))
    return Nat
typeof types (Boolean b     ) = return Bool
typeof types (IF te1 te2 te3) = do
    t1 <- typeof types te1
    case t1 of
        Bool           -> pure ()
        Nat            -> throwError $ Mismatch Nat Bool
        ty :-> ty'     -> throwError $ Mismatch t1 Bool
        TypeVariable n -> modify (over constraints (insert (Constraint (t1, Bool))))
    t2 <- typeof types te2
    t3 <- typeof types te3
    if null (fv t2) && null (fv t3)
        then (if t2 /= t3 then throwError $ Mismatch t2 t3 else return t2)
        else do
            modify (over constraints (insert (Constraint (t2, t3))))
            return t2

