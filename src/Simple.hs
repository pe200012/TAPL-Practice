module Simple where

import           Control.Exception              ( Exception
                                                , throw
                                                )
import           Data.Set
import           Prelude                 hiding ( pred
                                                , succ
                                                )

newtype Simple = Simple [Term]

data Term = TTrue Info
          | TFalse Info
          | IF Info Term Term Term
          | Zero Info
          | Succ Info Term
          | Pred Info Term
          | IsZero Info Term
          deriving (Show, Eq, Ord)

data Info = Info
    deriving (Show, Eq, Ord)

{-|

>>> isZero (Zero Info)
TTrue Info

>>> isZero (Succ Info (Zero Info))
TFalse Info

-}
isZero :: Term -> Term
isZero (Zero _) = TTrue Info
isZero _        = TFalse Info

{-|

>>> isZero (pred (succ (Zero Info)))
TTrue Info

-}
succ :: Term -> Term
succ = Succ Info

pred :: Term -> Term
pred (Zero _  ) = Zero Info
pred (Succ _ n) = n

consts :: Term -> Set Term
consts (Zero _    ) = singleton (Zero Info)
consts (Succ _ n  ) = consts n
consts (Pred _ n  ) = consts n
consts (TTrue  _  ) = singleton (TTrue Info)
consts (TFalse _  ) = singleton (TFalse Info)
consts (IsZero _ n) = consts n
consts (IF _ a b c) = consts a `union` consts b `union` consts c

tSize :: Term -> Int
tSize (TTrue  _  ) = 1
tSize (TFalse _  ) = 1
tSize (Zero   _  ) = 1
tSize (Succ   _ n) = tSize n + 1
tSize (Pred   _ n) = tSize n + 1
tSize (IsZero _ n) = tSize n + 1
tSize (IF _ a b c) = sum (tSize <$> [a, b, c]) + 1

depth :: Term -> Int
depth (TTrue  _  ) = 1
depth (TFalse _  ) = 1
depth (Zero   _  ) = 1
depth (Succ   _ n) = depth n + 1
depth (Pred   _ n) = depth n + 1
depth (IsZero _ n) = depth n + 1
depth (IF _ a b c) = maximum (depth <$> [a, b, c]) + 1

isNumeric :: Term -> Bool
isNumeric (Zero _   ) = True
isNumeric (Succ _ t1) = isNumeric t1
isNumeric _           = False

isVal :: Term -> Bool
isVal (TTrue  _) = True
isVal (TFalse _) = True
isVal t | isNumeric t = True
        | otherwise   = False

data NoRuleApplies = NoRuleApplies
    deriving Show
instance Exception NoRuleApplies

{- 

-- primitive values
>>> eval <$> [TTrue Info, TFalse Info, Zero Info]
[TTrue Info,TFalse Info,Zero Info]

-- successor natural number
>>> eval (Succ Info (Zero Info))
Succ Info (Zero Info)

-- preceding natural number
>>> eval (Pred Info (Succ Info (Zero Info)))
Zero Info

-- note that pred(zero) -> zero
>>> eval (Succ Info (Pred Info (Zero Info)))
Succ Info (Zero Info)

-- boolean function
>>> eval . IsZero Info <$> [Zero Info, Succ Info (Zero Info), Pred Info (Succ Info (Zero Info))]
[TTrue Info,TFalse Info,TTrue Info]

-- if statement: S-IFTrue Rule
>>> eval (IF Info (TTrue Info) (Zero Info) (Succ Info (Zero Info)))
Zero Info

-- if statement: S-IFFalse Rule
>>> eval (IF Info (TFalse Info) (Zero Info) (Succ Info (Zero Info)))
Succ Info (Zero Info)

-- type error
>>> eval (Succ Info (TTrue Info))
Succ Info (TTrue Info)

-}

eval1 :: Term -> Either NoRuleApplies Term
eval1 (IF _  (TTrue  _) t2 t3)                = Right t2
eval1 (IF _  (TFalse _) t2 t3)                = Right t3
eval1 (IF fi t1         t2 t3)                = eval1 t1 >>= \t1' -> Right $ IF fi t1' t2 t3
eval1 (Succ fi t1            )                = eval1 t1 >>= \t1' -> Right $ Succ fi t1'
eval1 (Pred _  (Zero _)      )                = Right $ Zero Info
eval1 (Pred _ (Succ _ nv1)) | isNumeric nv1   = Right nv1
eval1 (Pred   fi t1      )                    = eval1 t1 >>= \t1' -> Right $ Pred fi t1'
eval1 (IsZero _  (Zero _))                    = Right $ TTrue Info
eval1 (IsZero _ (Succ _ nv1)) | isNumeric nv1 = Right $ TFalse Info
eval1 (IsZero fi t1)                          = eval1 t1 >>= \t1' -> Right $ IsZero fi t1'
eval1 _                                       = Left NoRuleApplies

-- | small-step semantics
eval :: Term -> Term
eval t = case eval1 t of
    Left  _ -> t
    Right x -> eval x

{- 

-- Again, this time with eval'

>>> eval <$> [TTrue Info, TFalse Info, Zero Info]
[TTrue Info,TFalse Info,Zero Info]

>>> eval (Succ Info (Zero Info))
Succ Info (Zero Info)

>>> eval (Pred Info (Succ Info (Zero Info)))
Zero Info

>>> eval (Succ Info (Pred Info (Zero Info)))
Succ Info (Zero Info)

>>> eval . IsZero Info <$> [Zero Info, Succ Info (Zero Info), Pred Info (Succ Info (Zero Info))]
[TTrue Info,TFalse Info,TTrue Info]

>>> eval (IF Info (TTrue Info) (Zero Info) (Succ Info (Zero Info)))
Zero Info

>>> eval (IF Info (TFalse Info) (Zero Info) (Succ Info (Zero Info)))
Succ Info (Zero Info)

>>> eval (Succ Info (TTrue Info))
Succ Info (TTrue Info)

-}

-- | big-step semantics
eval' :: Term -> Term
eval' (Zero   _)               = Zero Info
eval' (TTrue  _)               = TTrue Info
eval' (TFalse _)               = TFalse Info
eval' (Succ _ n) | isNumeric n = Succ Info (eval' n)
eval' (Pred _ n) | isNumeric n = case eval' n of
    Zero _   -> Zero Info
    Succ _ n -> n
eval' (IsZero _ (Zero _  )) = TTrue Info
eval' (IsZero _ (Succ _ _)) = TFalse Info
eval' (IF _ a b c         ) = case eval' a of
    TTrue  _ -> eval' b
    TFalse _ -> eval' c
eval' t = t