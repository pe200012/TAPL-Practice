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

>>> prettytypeof = (.) (fmap prettyprintSimpleType) . typeof

>>> getType 0 cxt
Nothing

>>> getType 0 (bind SimpleBool cxt)
Just SimpleBool

>>> prettytypeof SimpleTrue cxt
Right "SimpleBool"

>>> prettytypeof SimpleFalse cxt
Right "SimpleBool"

>>> prettytypeof (SimpleIf SimpleTrue SimpleTrue SimpleFalse) cxt
Right "SimpleBool"

>>> arr = SimpleAbs SimpleBool SimpleTrue
>>> prettytypeof arr cxt
Right "SimpleBool -> SimpleBool"

>>> prettytypeof (SimpleIf SimpleTrue arr arr) cxt
Right "SimpleBool -> SimpleBool"

>>> prettytypeof (SimpleIf (SimpleAbs SimpleBool SimpleTrue) SimpleTrue SimpleFalse) cxt
Left "typeof, if-guard type mismatch: expected Boolean, but got (SimpleAbs SimpleBool SimpleTrue: SimpleBool -> SimpleBool)"

>>> prettytypeof (SimpleIf SimpleTrue arr SimpleFalse) cxt
Left "typeof, if-branch type mismatch: then SimpleBool -> SimpleBool, else SimpleBool"

>>> prettytypeof (SimpleVar 0 0) (bind SimpleBool cxt)
Right "SimpleBool"

>>> prettytypeof (SimpleVar 0 1) (bind SimpleBool cxt)
Left "typeof, error when getting type of variable: index 1"

>>> prettytypeof (SimpleAbs SimpleBool SimpleTrue) cxt
Right "SimpleBool -> SimpleBool"

>>> prettytypeof (SimpleAbs SimpleBool arr) cxt
Right "SimpleBool -> SimpleBool -> SimpleBool"

>>> prettytypeof (SimpleApp arr SimpleTrue) cxt
Right "SimpleBool"

>>> prettytypeof (SimpleApp SimpleTrue SimpleTrue) cxt
Left "typeof, expected SimpleArrow type, but got (SimpleTrue: SimpleBool)"

>>> prettytypeof (SimpleApp arr arr) cxt
Left "typeof, arrow parameter type mismatch: expected SimpleBool, but got (SimpleAbs SimpleBool SimpleTrue: SimpleBool -> SimpleBool)"

-}

prettyprintSimpleType :: SimpleType -> String
prettyprintSimpleType SimpleBool          = "SimpleBool"
prettyprintSimpleType (SimpleArrow t1 t2) = case t1 of
    SimpleArrow _ _ -> unpack (format "({}) -> {}" (prettyprintSimpleType <$> [t1, t2]))
    _               -> unpack (format "{} -> {}" (prettyprintSimpleType <$> [t1, t2]))

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
            then Left (unpack (format "typeof, if-guard type mismatch: expected Boolean, but got ({}: {})" [show g, prettyprintSimpleType g']))
            else do
                t1' <- typeof t1 cxt
                t2' <- typeof t2 cxt
                if t1' /= t2'
                    then Left (unpack (format "typeof, if-branch type mismatch: then {}, else {}" (prettyprintSimpleType <$> [t1', t2'])))
                    else Right t2'
    SimpleVar _  index -> maybe (Left (unpack (format "typeof, error when getting type of variable: index {}" [show index]))) Right (getType index cxt)
    SimpleAbs t  t1    -> Right . SimpleArrow t =<< typeof t1 (bind t cxt)
    SimpleApp t1 t2    -> do
        t1' <- typeof t1 cxt
        t2' <- typeof t2 cxt
        case t1' of
            SimpleArrow t11 t12
                | t2' == t11
                -> Right t12
                | otherwise
                -> Left
                    (unpack
                        (format "typeof, arrow parameter type mismatch: expected {}, but got ({}: {})"
                                [prettyprintSimpleType t11, show t2, prettyprintSimpleType t2']
                        )
                    )
            _ -> Left (unpack (format "typeof, expected SimpleArrow type, but got ({}: {})" [show t1, prettyprintSimpleType t1']))
