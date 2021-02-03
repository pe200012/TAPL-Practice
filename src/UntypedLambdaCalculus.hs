module UntypedLambdaCalculus where

import           Prelude                 hiding ( and
                                                , not
                                                , or
                                                , fst
                                                , snd
                                                )

type Name = String

data Term = Variable Name
          | Abstraction (Term -> Term)
          | Application (Term, Term)

instance Show Term where
    show (Variable    n     ) = "Variable " ++ n
    show (Abstraction _     ) = "Abstraction <opaque>"
    show (Application (a, b)) = "Application (" ++ show a ++ ", " ++ show b ++ ")"

var :: Name -> Term
var = Variable

abstract :: (Term -> Term) -> Term
abstract = Abstraction

apply :: (Term, Term) -> Term
apply = Application

-- | Church Boolean True
tru :: Term
tru = abstract (\t -> abstract (\f -> t))

-- | Church Boolean False
fls :: Term
fls = abstract (\t -> abstract (\f -> f))

{-
>>> f b = apply (apply (apply (test,b),var "true"),var "false")

>>> debug (f tru)
Variable true

>>> debug (f fls)
Variable false

>>> and' a b = apply (apply (and, a), b)

>>> debug (f (and' tru tru))
Variable true

>>> debug (f (and' fls tru))
Variable false

>>> debug (f (and' tru fls))
Variable false

>>> debug (f (and' fls fls))
Variable false

>>> or' a b = apply (apply (or, a), b)

>>> debug (f (or' tru tru))
Variable true

>>> debug (f (or' tru fls))
Variable true

>>> debug (f (or' fls tru))
Variable true

>>> debug (f (or' fls fls))
Variable false

>>> not' a = apply (not, a)

>>> debug (f (not' tru))
Variable false

>>> debug (f (not' fls))
Variable true

-}

-- | If-statement
test :: Term
test = abstract (\l -> abstract (\m -> abstract (\n -> apply (apply (l, m), n))))

-- | simple evaluation, without involving variable substitution
debug :: Term -> Term
debug (Variable    n     ) = Variable n
debug (Abstraction f     ) = Abstraction f
debug (Application (a, b)) = case debug a of
    Abstraction f -> debug (f b')
    _             -> Application (a, b')
    where b' = debug b

and :: Term
and = abstract (\b -> abstract (\c -> apply (apply (b, c), fls)))

or :: Term
or = abstract (\b -> abstract (\c -> apply (apply (b, tru), apply (apply (c, tru), fls))))

not :: Term
not = abstract (\b -> apply (apply (b, fls), tru))

{-
>>> pair' a b = apply (apply (pair, a), b)
>>> fst' p = apply (fst, p)
>>> snd' p = apply (snd, p)
>>> p = pair' (var "a") (var "b")

>>> debug (fst' p)
Variable a

>>> debug (snd' p)
Variable b

-}

pair :: Term
pair = abstract (\f -> abstract (\s -> abstract (\b -> apply (apply (b, f), s))))

fst :: Term
fst = abstract (\p -> apply (p, tru))

snd :: Term
snd = abstract (\p -> apply (p, fls))
