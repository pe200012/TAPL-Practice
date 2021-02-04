{-# LANGUAGE NoImplicitPrelude #-}
module UntypedLambdaCalculus where




import Prelude (String, Show(show), (++), const, undefined)
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

-- $setup
-- >>> trueorfalse b = apply (apply (apply (test,b),var "true"),var "false")

{-
>>> f = trueorfalse

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

{-

>>> debug (trueorfalse (apply (iszro, c_0)))
Variable true

>>> debug (trueorfalse (apply (iszro, c_1)))
Variable false

>>> debug (trueorfalse (apply (iszro, apply (apply (times, c_0), c_1))))
Variable true

>>> debug (trueorfalse (apply (iszro, apply (prd, c_0))))
Variable true

>>> debug (trueorfalse (apply (iszro, apply (prd, c_1))))
Variable true

>>> debug (trueorfalse (apply (iszro, apply (prd, c_2))))
Variable false

>>> debug (trueorfalse (apply (iszro, apply (apply (subtract, c_1), c_1))))
Variable true

>>> debug (trueorfalse (apply (iszro, apply (apply (subtract, c_0), c_1))))
Variable true

>>> debug (trueorfalse (apply (iszro, apply (apply (subtract, c_2), c_1))))
Variable false

>>> debug (trueorfalse (apply (apply (equal, c_0), c_0)))
Variable true

>>> debug (trueorfalse (apply (apply (equal, c_1), c_0)))
Variable false

>>> debug (trueorfalse (apply (apply (equal, c_0), c_1)))
Variable false

>>> debug (trueorfalse (apply (apply (equal, c_2), apply (apply (times, c_1), c_2))))
Variable true

-}

c_0 :: Term
c_0 = abstract (\s -> abstract (\z -> z))

c_1 :: Term
c_1 = abstract (\s -> abstract (\z -> apply (s, z)))

c_2 :: Term
c_2 = abstract (\s -> abstract (\z -> apply (s, apply (s, z))))

scc :: Term
scc = abstract (\n -> abstract (\s -> abstract (\z -> apply (s, apply (apply (n, s), z)))))

plus :: Term
plus = abstract (\m -> abstract (\n -> abstract (\s -> abstract (\z -> apply (apply (m, s), apply (apply (n, s), z))))))

times :: Term
times = abstract (\m -> abstract (\n -> abstract (\s -> apply (m, apply (n, s)))))

power :: Term
power = abstract (\m -> abstract (\n -> apply (n, m)))

iszro :: Term
iszro = abstract (\m -> apply (apply (m, abstract (const fls)), tru))

zz :: Term
zz = apply (apply (pair, c_0), c_0)

ss :: Term
ss = abstract (\p -> apply (apply (pair, apply (snd, p)), apply (apply (plus, c_1), apply (snd, p))))

prd :: Term
prd = abstract (\m -> apply (fst, apply (apply (m, ss), zz)))

subtract :: Term
subtract = abstract (\m -> abstract (\n -> apply (apply (n, prd), m)))

equal :: Term
equal = abstract (\m -> abstract (\n -> apply (apply (and, r m n), r n m)))
    where r m n = apply (iszro, apply (apply (subtract, m), n))


