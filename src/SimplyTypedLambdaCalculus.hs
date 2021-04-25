{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
module SimplyTypedLambdaCalculus where


import           Control.Applicative            ( (<|>) )
import           Data.HashMap.Lazy              ( HashMap
                                                , insert
                                                , lookup
                                                )
import qualified Data.HashMap.Lazy             as HashMap
import qualified Data.HashMap.Lazy             as Map
import           Data.List                      ( elemIndex )
import           Data.Maybe                     ( fromJust )
import           Data.Set                       ( Set
                                                , member
                                                , notMember
                                                , singleton
                                                , union
                                                )
import qualified Data.Set                      as Set
import           Data.Text.Format               ( Format
                                                , format
                                                )
import           Data.Text.Lazy                 ( unpack )
import           Prelude                 hiding ( lookup )

newtype Context = Context { unContext :: HashMap String SimpleType } deriving Show

data SimpleType = SimpleBool
                | SimpleUnit
                | SimpleProduct SimpleType SimpleType
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
          | SimplePair Term Term
          | SimpleFst Term
          | SimpleSnd Term
          deriving Show

{-

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

>>> prettytypeof (SimplePair SimpleTrue SimpleFalse) cxt
Right "SimpleBool * SimpleBool"

>>> prettytypeof (SimplePair SimpleTrue arr) cxt
Right "SimpleBool * (SimpleBool -> SimpleBool)"

>>> prettytypeof (SimplePair arr arr) cxt
Right "(SimpleBool -> SimpleBool) * (SimpleBool -> SimpleBool)"

>>> prettytypeof (SimpleFst (SimplePair SimpleTrue arr)) cxt
Right "SimpleBool"

>>> prettytypeof (SimpleSnd (SimplePair SimpleTrue arr)) cxt
Right "SimpleBool -> SimpleBool"

-}

fv :: Term -> Set String
fv SimpleTrue        = Set.empty
fv SimpleFalse       = Set.empty
fv Unit              = Set.empty
fv (SimpleIf a b c ) = fv a `union` fv b `union` fv c
fv (SimpleVar n    ) = singleton n
fv (SimpleLet n a b) = fv a `union` Set.delete n (fv b)
fv (SimpleAbs n _ t) = Set.delete n (fv t)
fv (SimpleApp  a b ) = fv a `union` fv b
fv (SimplePair a b ) = fv a `union` fv b
fv (SimpleFst t    ) = fv t
fv (SimpleSnd t    ) = fv t

sealArrow :: SimpleType -> Format
sealArrow (SimpleArrow _ _) = "({})"
sealArrow _                 = "{}"

prettyprintSimpleType :: SimpleType -> String
prettyprintSimpleType SimpleBool            = "SimpleBool"
prettyprintSimpleType (SimpleProduct t1 t2) = unpack (format (sealArrow t1 <> " * " <> sealArrow t2) (prettyprintSimpleType <$> [t1, t2]))
prettyprintSimpleType (SimpleArrow   t1 t2) = unpack (format (sealArrow t1 <> " -> {}") (prettyprintSimpleType <$> [t1, t2]))
prettyprintSimpleType SimpleUnit            = "SimpleUnit"

context :: HashMap String SimpleType -> Context
context = Context

emptyContext :: Context
emptyContext = Context (HashMap.fromList [])

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
    SimplePair t1 t2 -> SimpleProduct <$> typeof t1 cxt <*> typeof t2 cxt
    SimpleFst t      -> do
        t' <- typeof t cxt
        case t' of
            SimpleProduct a _ -> Right a
            _                 -> Left (unpack (format "typeof, expected SimplePair type, but got ({}: {})" [show t, prettyprintSimpleType t']))
    SimpleSnd t -> do
        t' <- typeof t cxt
        case t' of
            SimpleProduct _ b -> Right b
            _                 -> Left (unpack (format "typeof, expected SimplePair type, but got ({}: {})" [show t, prettyprintSimpleType t']))

{-

>>> eval SimpleTrue
SimpleTrue

>>> eval SimpleFalse
SimpleFalse

>>> eval Unit
Unit

>>> eval $ SimpleIf SimpleTrue (SimpleAbs "x" SimpleUnit SimpleTrue) (SimpleAbs "y" SimpleUnit SimpleFalse)
SimpleAbs "x" SimpleUnit SimpleTrue

>>> eval $ SimpleIf SimpleFalse (SimpleAbs "x" SimpleUnit SimpleTrue) (SimpleAbs "y" SimpleUnit SimpleFalse)
SimpleAbs "y" SimpleUnit SimpleFalse

>>> eval $ SimpleIf Unit SimpleTrue SimpleFalse
typeof, if-guard type mismatch: expected Boolean, but got (Unit: SimpleUnit)

>>> eval $ SimpleIf SimpleTrue SimpleFalse Unit
typeof, if-branch type mismatch: then SimpleBool, else SimpleUnit

>>> eval $ SimpleVar "x"
typeof, error when getting type of variable: x

>>> eval $ SimpleLet "x" Unit (SimpleVar "x")
Unit

>>> eval $ SimpleLet "x" Unit (SimpleLet "x" SimpleTrue (SimpleVar "x"))
SimpleTrue

>>> eval $ SimpleAbs "x" SimpleBool (SimpleIf (SimpleVar "x") SimpleTrue SimpleFalse)
SimpleAbs "x" SimpleBool (SimpleIf (SimpleVar "x") SimpleTrue SimpleFalse)

>>> eval $ SimpleApp (SimpleAbs "x" SimpleBool (SimpleIf (SimpleVar "x") SimpleTrue SimpleFalse)) SimpleTrue
SimpleTrue

>>> eval $ SimplePair SimpleTrue Unit
SimplePair SimpleTrue Unit

>>> eval $ SimpleFst $ SimplePair SimpleTrue Unit
SimpleTrue

>>> eval $ SimpleSnd $ SimplePair SimpleTrue Unit
Unit

-}

eval :: Term -> Term
eval t = case typeof t emptyContext of
    Left  x -> error x
    Right _ -> stepWrap (Right (Map.empty, t))
  where
    stepWrap = either id (stepWrap . uncurry step)
    step _   SimpleTrue       = Left SimpleTrue
    step _   SimpleFalse      = Left SimpleFalse
    step _   Unit             = Left Unit
    step cxt (SimpleIf g a b) = case step cxt g of
        Left g' -> case g' of
            SimpleTrue  -> Right (cxt, a)
            SimpleFalse -> Right (cxt, b)
            _           -> error "SimpleIf: impossible to reach here"
        Right (cxt', g'') -> Right (cxt', SimpleIf g'' a b)
    step cxt (SimpleVar s    ) = Right (cxt, fromJust (lookup s cxt))
    step cxt (SimpleLet n a b) = case step (Map.insert n a cxt) b of
        Left  x       -> Left x
        Right (_, x') -> Right (cxt, x')
    step cxt abs@SimpleAbs{} = Left abs
    step cxt (SimpleApp a b) = case step cxt a of
        Right (cxt', a')        -> Right (cxt', SimpleApp a' b)
        Left  (SimpleAbs n t x) -> case step cxt b of
            Right (cxt'', b') -> Right (cxt'', SimpleApp a b')
            Left  b''         -> Right (cxt, subst (n, b) x)
        Left _ -> error "SimpleApp: impossible to reach here"
      where
        rename _ SimpleTrue       = SimpleTrue
        rename _ SimpleFalse      = SimpleFalse
        rename _ Unit             = Unit
        rename p (SimpleIf g a b) = SimpleIf (rename p g) (rename p a) (rename p b)
        rename (n, n0) (SimpleVar n') | n == n'   = SimpleVar n0
                                      | otherwise = SimpleVar n'
        rename p@(n, _) (SimpleLet n' a b) | n == n'   = SimpleLet n' a' b
                                           | otherwise = SimpleLet n' a' (rename p b)
            where a' = rename p a
        rename p@(n, _) (SimpleAbs n' t a) | n == n'   = SimpleAbs n' t a
                                           | otherwise = SimpleAbs n' t (rename p a)
        rename p (SimpleApp  a b) = SimpleApp (rename p a) (rename p b)
        rename p (SimplePair a b) = SimplePair (rename p a) (rename p b)
        rename p (SimpleFst a   ) = SimpleFst (rename p a)
        rename p (SimpleSnd a   ) = SimpleSnd (rename p a)
        subst _ SimpleTrue       = SimpleTrue
        subst _ SimpleFalse      = SimpleFalse
        subst _ Unit             = Unit
        subst p (SimpleIf g a b) = SimpleIf (subst p g) (subst p a) (subst p b)
        subst (b, x) (SimpleVar n) | n == b    = x
                                   | otherwise = SimpleVar n
        subst (b, x) (SimpleLet n a b') | n == b    = SimpleLet n a' b'
                                        | otherwise = SimpleLet n a' (subst (b, x) b')
            where a' = subst (b, x) a
        subst (b, x) (SimpleAbs n t b') | n /= b && n `notMember` fv x = SimpleAbs n t (subst (b, x) b')
                                        | n `member` fv x              = subst (b, x) (SimpleAbs (n ++ "'") t (rename (n, n ++ "'") b'))
                                        | otherwise                    = SimpleAbs n t b'
        subst (b, x) (SimpleApp  a b') = SimpleApp (subst (b, x) a) (subst (b, x) b')
        subst (b, x) (SimplePair a b') = SimplePair (subst (b, x) a) (subst (b, x) b')
        subst (b, x) (SimpleFst a    ) = SimpleFst (subst (b, x) a)
        subst (b, x) (SimpleSnd a    ) = SimpleSnd (subst (b, x) a)
    step cxt (SimplePair a b) = case step cxt a of
        Right (cxt', a') -> Right (cxt', SimplePair a' b)
        Left  a'         -> case step cxt b of
            Right (cxt', b') -> Right (cxt', SimplePair a' b')
            Left  b'         -> Left (SimplePair a' b')
    step cxt (SimpleFst a) = case step cxt a of
        Right (cxt', a')       -> Right (cxt', SimpleFst a')
        Left  (SimplePair x _) -> Left x
        Left  _                -> error "SimpleFst: Impossible to reach here"
    step cxt (SimpleSnd a) = case step cxt a of
        Right (cxt', a')       -> Right (cxt', SimpleFst a')
        Left  (SimplePair _ x) -> Left x
        Left  _                -> error "SimpleSnd: Impossible to reach here"
