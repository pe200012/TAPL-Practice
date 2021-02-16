{-# LANGUAGE OverloadedStrings #-}
module SimplyTypedLambdaCalculus where


import           Data.Maybe                     ( listToMaybe )
import           Data.Text.Format               ( format )
import           Data.Text.Lazy                 ( unpack )
import           Prelude                 hiding ( lookup )

newtype Context = Context { unContext :: [SimpleType] } deriving Show

data SimpleType = SimpleBool
                | SimpleArrow SimpleType SimpleType
                deriving (Show, Eq)

type TypeIndex = Int
type VarIndex = Int

data Term = SimpleTrue
          | SimpleFalse
          | SimpleIf Term Term Term
          | SimpleVar VarIndex TypeIndex
          | SimpleAbs SimpleType Term
          | SimpleApp Term Term
          deriving (Show)

{-

>>> cxt = context []
>>> bind SimpleBool cxt
Context {unContext = [SimpleBool]}

>>> getType 0 cxt
Nothing

>>> getType 0 (bind SimpleBool cxt)
Just SimpleBool

>>> typeof SimpleTrue cxt
Right SimpleBool

>>> typeof SimpleFalse cxt
Right SimpleBool

>>> typeof (SimpleIf SimpleTrue SimpleTrue SimpleFalse) cxt
Right SimpleBool

>>> arr = SimpleAbs SimpleBool SimpleTrue
>>> typeof arr cxt
Right (SimpleArrow SimpleBool SimpleBool)

>>> typeof (SimpleIf SimpleTrue arr arr) cxt
Right (SimpleArrow SimpleBool SimpleBool)

>>> typeof (SimpleIf (SimpleAbs SimpleBool SimpleTrue) SimpleTrue SimpleFalse) cxt
Left "typeof, if-guard type mismatch: expected Boolean, but got (SimpleAbs SimpleBool SimpleTrue: SimpleArrow SimpleBool SimpleBool)"

>>> typeof (SimpleIf SimpleTrue arr SimpleFalse) cxt
Left "typeof, if-branch type mismatch: then SimpleArrow SimpleBool SimpleBool, else SimpleBool"

>>> typeof (SimpleVar 0 0) (bind SimpleBool cxt)
Right SimpleBool

>>> typeof (SimpleVar 0 1) (bind SimpleBool cxt)
Left "typeof, error when getting type of variable: index 1"

>>> typeof (SimpleAbs SimpleBool SimpleTrue) cxt
Right (SimpleArrow SimpleBool SimpleBool)

>>> typeof (SimpleAbs SimpleBool arr) cxt
Right (SimpleArrow SimpleBool (SimpleArrow SimpleBool SimpleBool))

>>> typeof (SimpleApp arr SimpleTrue) cxt
Right SimpleBool

>>> typeof (SimpleApp SimpleTrue SimpleTrue) cxt
Left "typeof, expected SimpleArrow type, but got (SimpleTrue: SimpleBool)"

>>> typeof (SimpleApp arr arr) cxt
Left "typeof, arrow parameter type mismatch: expected SimpleBool, but got (SimpleAbs SimpleBool SimpleTrue: SimpleArrow SimpleBool SimpleBool)"

-}

context :: [SimpleType] -> Context
context = Context

bind :: SimpleType -> Context -> Context
bind b = Context . (:) b . unContext

getType :: Int -> Context -> Maybe SimpleType
getType index = listToMaybe . drop index . unContext

typeof :: Term -> Context -> Either String SimpleType
typeof t cxt = case t of
    SimpleTrue       -> Right SimpleBool
    SimpleFalse      -> Right SimpleBool
    SimpleIf g t1 t2 -> do
        g' <- typeof g cxt
        if g' /= SimpleBool
            then Left (unpack (format "typeof, if-guard type mismatch: expected Boolean, but got ({}: {})" [show g, show g']))
            else do
                t1' <- typeof t1 cxt
                t2' <- typeof t2 cxt
                if t1' /= t2' then Left (unpack (format "typeof, if-branch type mismatch: then {}, else {}" [show t1', show t2'])) else Right t2'
    SimpleVar _ index -> maybe (Left (unpack (format "typeof, error when getting type of variable: index {}" [show index]))) Right (getType index cxt)
    SimpleAbs t t1    -> Right . SimpleArrow t =<< typeof t1 (bind t cxt)
    SimpleApp t1 t2 -> do
        t1' <- typeof t1 cxt
        t2' <- typeof t2 cxt
        case t1' of
            SimpleArrow t11 t12 | t2' == t11 -> Right t12
                                | otherwise  -> Left (unpack (format "typeof, arrow parameter type mismatch: expected {}, but got ({}: {})" [show t11, show t2, show t2']))
            _                -> Left (unpack (format "typeof, expected SimpleArrow type, but got ({}: {})" [show t1, show t1']))
