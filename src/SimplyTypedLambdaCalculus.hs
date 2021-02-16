module SimplyTypedLambdaCalculus where

import           Data.Maybe                     ( listToMaybe )
import           Prelude                 hiding ( lookup )

newtype Context = Context { unContext :: [SimpleType] } deriving Show

data SimpleType = SimpleBool
                | SimpleArrow SimpleType SimpleType
                deriving Show

type TypeIndex = Int
type VarIndex = Int

data Term = SimpleTrue
          | SimpleFalse
          | SimpleIf Term Term Term
          | SimpleVar VarIndex TypeIndex
          | SimpleAbs SimpleType Term
          | SimpleApp Term Term

{-

>>> cxt = context []
>>> bind SimpleBool cxt
Context {unContext = [SimpleBool]}

>>> getType 0 cxt
Nothing

>>> getType 0 (bind SimpleBool cxt)
Just SimpleBool

-}

context :: [SimpleType] -> Context
context = Context

bind :: SimpleType -> Context -> Context
bind b = Context . (:) b . unContext

getType :: Int -> Context -> Maybe SimpleType
getType index = listToMaybe . drop index . unContext
