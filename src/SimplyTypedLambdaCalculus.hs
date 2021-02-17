{-# LANGUAGE OverloadedStrings #-}
module SimplyTypedLambdaCalculus where


import           Control.Applicative            ( (<|>) )
import           Data.HashMap.Lazy              ( HashMap
                                                , insert
                                                , lookup
                                                )
import qualified Data.HashMap.Lazy             as HashMap
import           Data.List                      ( elemIndex )
import           Data.Maybe                     ( fromJust )
import           Data.Set                       ( Set
                                                , singleton
                                                , union
                                                )
import qualified Data.Set                      as Set
import           Data.Text.Format               ( format )
import           Data.Text.Lazy                 ( unpack )
import           Prelude                 hiding ( lookup )
import qualified UntypedLambdaCalculus         as UTLC

newtype Context = Context { unContext :: HashMap String SimpleType } deriving Show

data SimpleType = SimpleBool
                | SimpleUnit
                | SimpleArrow SimpleType SimpleType
                deriving (Show, Eq)

data Term = SimpleTrue
          | SimpleFalse
          | Unit
          | SimpleIf Term Term Term
          | SimpleVar String
          | SimpleLet String Term Term
          | SimpleAbs String SimpleType Term
          | SimpleApp Term Term
          deriving Show

{-

>>> showHelper = error . UTLC.prettyTerm3 :: UTLC.Term3 -> ()
>>> cxt = context (HashMap.fromList [])
>>> bind "a" SimpleBool cxt
Context {unContext = fromList [("a",SimpleBool)]}

>>> prettytypeof = (.) (fmap prettyprintSimpleType) . typeof

>>> getType "a" cxt
Nothing

>>> getType "a" (bind "a" SimpleBool cxt)
Just SimpleBool

>>> prettytypeof SimpleTrue cxt
Right "SimpleBool"

>>> prettytypeof SimpleFalse cxt
Right "SimpleBool"

>>> prettytypeof (SimpleIf SimpleTrue SimpleTrue SimpleFalse) cxt
Right "SimpleBool"

>>> arr = SimpleAbs "x" SimpleBool SimpleTrue
>>> prettytypeof arr cxt
Right "SimpleBool -> SimpleBool"

>>> prettytypeof (SimpleIf SimpleTrue arr arr) cxt
Right "SimpleBool -> SimpleBool"

>>> prettytypeof (SimpleIf (SimpleAbs "x" SimpleBool SimpleTrue) SimpleTrue SimpleFalse) cxt
Left "typeof, if-guard type mismatch: expected Boolean, but got (SimpleAbs \"x\" SimpleBool SimpleTrue: SimpleBool -> SimpleBool)"

>>> prettytypeof (SimpleIf SimpleTrue arr SimpleFalse) cxt
Left "typeof, if-branch type mismatch: then SimpleBool -> SimpleBool, else SimpleBool"

>>> prettytypeof (SimpleVar "x") (bind "x" SimpleBool cxt)
Right "SimpleBool"

>>> prettytypeof (SimpleVar "y") (bind "x" SimpleBool cxt)
Left "typeof, error when getting type of variable: y"

>>> prettytypeof (SimpleAbs "x" SimpleBool SimpleTrue) cxt
Right "SimpleBool -> SimpleBool"

>>> prettytypeof (SimpleAbs "x" SimpleBool arr) cxt
Right "SimpleBool -> SimpleBool -> SimpleBool"

>>> prettytypeof (SimpleAbs "x" SimpleBool (SimpleVar "x")) cxt
Right "SimpleBool -> SimpleBool"

>>> prettytypeof (SimpleApp arr SimpleTrue) cxt
Right "SimpleBool"

>>> prettytypeof (SimpleApp SimpleTrue SimpleTrue) cxt
Left "typeof, expected SimpleArrow type, but got (SimpleTrue: SimpleBool)"

>>> prettytypeof (SimpleApp arr arr) cxt
Left "typeof, arrow parameter type mismatch: expected SimpleBool, but got (SimpleAbs \"x\" SimpleBool SimpleTrue: SimpleBool -> SimpleBool)"

>>> prettytypeof (SimpleAbs "x" (SimpleArrow SimpleBool SimpleBool) arr) cxt
Right "(SimpleBool -> SimpleBool) -> SimpleBool -> SimpleBool"

>>> prettytypeof (SimpleLet "x" SimpleTrue (SimpleVar "x")) cxt
Right "SimpleBool"

>>> prettytypeof (SimpleLet "x" SimpleTrue (SimpleAbs "y" SimpleBool (SimpleVar "x"))) cxt
Right "SimpleBool -> SimpleBool"

>>> showHelper (erase SimpleTrue (HashMap.fromList []))
(λ. (λ. 1))

>>> showHelper (erase arr (HashMap.fromList []))
(λ. (λ. (λ. 1)))

>>> showHelper (erase (SimpleAbs "x" (SimpleArrow SimpleBool SimpleBool) arr) (HashMap.fromList []))
(λ. (λ. (λ. (λ. 1))))

-}

fv :: Term -> Set String
fv SimpleTrue        = Set.empty
fv SimpleFalse       = Set.empty
fv Unit              = Set.empty
fv (SimpleIf a b c ) = fv a `union` fv b `union` fv c
fv (SimpleVar n    ) = singleton n
fv (SimpleLet n a b) = fv a `union` Set.delete n (fv b)
fv (SimpleAbs n _ t) = Set.delete n (fv t)
fv (SimpleApp a b  ) = fv a `union` fv b

prettyprintSimpleType :: SimpleType -> String
prettyprintSimpleType SimpleBool          = "SimpleBool"
prettyprintSimpleType (SimpleArrow t1 t2) = case t1 of
    SimpleArrow _ _ -> unpack (format "({}) -> {}" (prettyprintSimpleType <$> [t1, t2]))
    _               -> unpack (format "{} -> {}" (prettyprintSimpleType <$> [t1, t2]))

context :: HashMap String SimpleType -> Context
context = Context

bind :: String -> SimpleType -> Context -> Context
bind n t = Context . insert n t . unContext

getType :: String -> Context -> Maybe SimpleType
getType n = lookup n . unContext

typeof :: Term -> Context -> Either String SimpleType
typeof t cxt = case t of
    SimpleTrue       -> Right SimpleBool
    SimpleFalse      -> Right SimpleBool
    Unit             -> Right SimpleUnit
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
    SimpleVar n       -> maybe (Left (unpack (format "typeof, error when getting type of variable: {}" n))) Right (getType n cxt)
    SimpleLet n t1 t2 -> do
        t1' <- typeof t1 cxt
        typeof t2 (bind n t1' cxt)
    SimpleAbs n t t1 -> Right . SimpleArrow t =<< typeof t1 (bind n t cxt)
    SimpleApp t1 t2  -> do
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

erase :: Term -> HashMap String Int -> UTLC.Term3
erase t c = erase' [] t
  where
    erase' _  SimpleTrue        = UTLC.Abstraction3 (UTLC.Abstraction3 (UTLC.Index 1))
    erase' _  SimpleFalse       = UTLC.Abstraction3 (UTLC.Abstraction3 (UTLC.Index 0))
    erase' bv Unit              = erase' bv SimpleFalse
    erase' bv (SimpleIf g a b ) = UTLC.Application3 (UTLC.Application3 (erase' bv g) (erase' bv a)) (erase' bv b)
    erase' bv (SimpleVar n    ) = fromJust (UTLC.Index <$> (elemIndex n bv <|> lookup n c))
    erase' bv (SimpleLet n a b) = UTLC.Application3 (UTLC.Abstraction3 (erase' (n : bv) b)) (erase' bv a)
    erase' bv (SimpleAbs n _ t) = UTLC.Abstraction3 (erase' (n : bv) t)
    erase' bv (SimpleApp a b  ) = UTLC.Application3 (erase' bv a) (erase' bv b)

eval :: Term -> HashMap String Int -> UTLC.Term3
eval = (.) UTLC.eval . erase
