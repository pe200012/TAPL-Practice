{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
module Polymorphism where

import           Control.Lens                   ( (^.)
                                                , over
                                                , view
                                                )
import           Control.Lens.TH
import           Control.Monad                  ( unless )
import           Control.Monad.Except           ( Except
                                                , ExceptT
                                                , MonadError(throwError)
                                                , runExcept
                                                , runExceptT
                                                )
import           Control.Monad.State.Lazy       ( MonadState
                                                , State
                                                , evalState
                                                , execState
                                                , gets
                                                , modify
                                                , runState
                                                )
import           Data.Maybe                     ( fromMaybe )
import           Data.Sequence                  ( Seq
                                                , (|>)
                                                )
import qualified Data.Sequence                 as Seq
import           Data.Set                       ( Set
                                                , empty
                                                , fromList
                                                , insert
                                                , maxView
                                                , minView
                                                , notMember
                                                , singleton
                                                , union
                                                )
import qualified Data.Set                      as Set

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
    (Constraint (a, b)) == (Constraint (c, d)) = (a == c) && (b == d) || (a == d) && (b == c)

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

maxTV :: Term -> Int
maxTV (Lam (ty' :-> ty2   ) te) = max (maxTV te) $ maybe 0 fst (maxView (fv ty' `union` fv ty2))
maxTV (Lam (TypeVariable n) te) = max n (maxTV te)
maxTV (Lam _                te) = maxTV te
maxTV (Var n                  ) = 0
maxTV (App te te'             ) = max (maxTV te) (maxTV te')
maxTV Zro                       = 0
maxTV (Suc     te   )           = maxTV te
maxTV (Boolean b    )           = 0
maxTV (IF te te' te2)           = max (max (maxTV te) (maxTV te')) (maxTV te2)

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

>>> typeof' [] (Lam (TypeVariable 0) (Var 0))
(Right (TypeVariable 0 :-> TypeVariable 0),TypeCheckContext {_constraints = fromList [], _nextTV = 0})

>>> typeof' [] (App (Lam (TypeVariable 0) (Var 0)) Zro)
(Right (TypeVariable 0),TypeCheckContext {_constraints = fromList [Constraint (TypeVariable 0,Nat)], _nextTV = 0})

>>> typeof' [] (App (App (Lam (TypeVariable 0) (Var 0)) Zro) (IF (Boolean True) Zro Zro))
(Right (TypeVariable 0),TypeCheckContext {_constraints = fromList [Constraint (TypeVariable 0,Nat),Constraint (TypeVariable 0,Nat :-> TypeVariable 0)], _nextTV = 1})

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
            m <- fetchTV
            modify (over constraints (insert (Constraint (t1, t2 :-> TypeVariable m))))
            return $ TypeVariable m
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

class Substitution a where
    subst :: (Type, Type) -> a -> a

instance Substitution Type where
    subst (a, b) t | a == t    = b
                   | otherwise = t

instance Substitution Constraint where
    subst p (Constraint (a, b)) = Constraint (subst p a, subst p b)

data UnificationError = RecursiveType Type
                      | NoSolution Constraint
    deriving Show

{-

>>> genConstants t = execState (runExceptT (typeof [] t)) (TypeCheckContext empty 0)

>>> runExcept . unify $ genConstants (Lam Nat (Var 0)) ^. constraints
Right (fromList [])

>>> runExcept . unify $ genConstants (App (App (Lam (TypeVariable 0) (Var 0)) Zro) (IF (Boolean True) Zro Zro)) ^. constraints
Left (NoSolution (Constraint (Nat,Nat :-> TypeVariable 0)))

>>>(`runState` (TypeCheckContext empty 0)) $ runExceptT $ typeof [] (App (App (Lam (TypeVariable 0) (Var 0)) Zro) (IF (Boolean True) Zro Zro))
(Right (TypeVariable 0),TypeCheckContext {_constraints = fromList [Constraint (TypeVariable 0,Nat),Constraint (TypeVariable 0,Nat :-> TypeVariable 0)], _nextTV = 1})

-}

unify :: Set Constraint -> Except UnificationError (Seq (Type, Type))
unify constraints = case minView constraints of
    Nothing -> return Seq.empty
    Just (Constraint (t1, t2), constraints') -> if t1 == t2
        then unify constraints'
        else case t1 of
            TypeVariable n
                | notMember n (fv t2) -> do
                    s <- unify (Set.map (subst (t1, t2)) constraints')
                    return $ s |> (t1, t2)
                | otherwise -> throwError $ RecursiveType t1
            t11 :-> t12 ->
                (case t2 of
                    TypeVariable n
                        | notMember n (fv t1) -> do
                            s <- unify (Set.map (subst (t2, t1)) constraints')
                            return $ s |> (t2, t1)
                        | otherwise -> throwError $ RecursiveType t2
                    t21 :-> t22 -> unify (constraints' <> fromList [Constraint (t11, t21), Constraint (t12, t22)])
                    _           -> throwError $ NoSolution (Constraint (t1, t2))
                )
            _ -> throwError $ NoSolution (Constraint (t1, t2))

{-

>>> typecheck' = runExcept . typecheck

>>> typecheck' Zro
Right Nat

>>> typecheck' $ Suc Zro
Right Nat

>>> typecheck' $ Boolean True
Right Bool

>>> typecheck' $ App (App (Lam (TypeVariable 1) (Lam (TypeVariable 2) (Var 0))) (Boolean False)) Zro
Right Nat

>>> typecheck' $ App (App (Lam (TypeVariable 1) (Lam (TypeVariable 2) (Var 1))) (Boolean False)) Zro
Right Bool

>>> typecheck' $ App (App (Lam (TypeVariable 1) (Lam (TypeVariable 2) (Suc (Var 1)))) (Boolean False)) Zro
Left (Right (NoSolution (Constraint (Bool,Nat))))

-}

typecheck :: Term -> Except (Either TypeError UnificationError) Type
typecheck t = case runState (runExceptT (typeof [] t)) (TypeCheckContext empty (maxTV t + 1)) of
    (Left  e , _ ) -> throwError $ Left e
    (Right t', cs) -> case runExcept (unify (cs ^. constraints)) of
        Left  e  -> throwError $ Right e
        Right ss -> return $ foldr subst t' ss
