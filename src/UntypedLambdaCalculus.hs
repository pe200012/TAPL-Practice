{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module UntypedLambdaCalculus where


import           Control.Applicative            ( (<|>) )
import           Control.Monad                  ( when )
import           Control.Monad.State.Lazy       ( State
                                                , StateT
                                                , get
                                                , modify
                                                , runState
                                                )
import           Data.HashMap.Lazy              ( HashMap
                                                , empty
                                                , fromList
                                                , insert
                                                , lookup
                                                )
import           Data.List                      ( elemIndex )
import           Data.Maybe                     ( fromJust
                                                , fromMaybe
                                                , isJust
                                                , isNothing
                                                )
import           Data.Set                       ( Set
                                                , delete
                                                , member
                                                , notMember
                                                , singleton
                                                , union
                                                )
import           Data.Text.Format               ( format )
import           Data.Text.Lazy                 ( unpack )
import           Prelude                 hiding ( and
                                                , fst
                                                , head
                                                , lookup
                                                , not
                                                , or
                                                , snd
                                                , subtract
                                                , tail
                                                )
import qualified Prelude

type Name = String

-- | Lambda term definition, borrowing host language's lambda feature to implement substituition
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
c_0 = fls

c_1 :: Term
c_1 = abstract (\s -> abstract (\z -> apply (s, z)))

c_2 :: Term
c_2 = abstract (\s -> abstract (\z -> apply (s, apply (s, z))))

c_3 :: Term
c_3 = abstract (\s -> abstract (\z -> apply (s, apply (s, apply (s, z)))))

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
equal = abstract (\m -> abstract (\n -> apply (apply (and, r m n), r n m))) where r m n = apply (iszro, apply (apply (subtract, m), n))

{-

>>> single = apply (apply (cons, c_0), nil)

>>> debug (trueorfalse (apply (isNil, nil)))
Variable true

>>> debug (trueorfalse (apply (isNil, apply (apply (cons, c_1), nil))))
Variable false

>>> debug (trueorfalse (apply (isNil, apply (head, nil))))
Variable true

>>> debug (trueorfalse (apply (apply (equal, c_1), apply (head, apply (apply (cons, c_1), nil)))))
Variable true

>>> debug (trueorfalse (apply (apply (equal, c_2), apply (head, apply (apply (cons, c_1), nil)))))
Variable false

>>> debug (trueorfalse (apply (isNil, apply (tail, nil))))
Variable true

>>> debug (trueorfalse (apply (isNil, apply (tail, apply (apply (cons, c_1), nil)))))
Variable true

>>> debug (trueorfalse (apply (isNil, apply (apply (cons, c_1), apply (apply (cons, c_1), nil)))))
Variable false

>>> debug (trueorfalse (apply (isNil, apply (apply (cons, c_1),(apply (apply (cons, c_1), apply (apply (cons, c_1), nil)))))))
Variable false

-}

nil :: Term
nil = fls

isNil :: Term
isNil = abstract (\ls -> apply (apply (ls, hole), tru)) where hole = abstract (const (abstract (const fls)))

cons :: Term
cons = abstract (\h -> abstract (\ls -> abstract (\c -> abstract (\n -> apply (apply (c, h), apply (apply (ls, c), n))))))

head :: Term
head = abstract (\ls -> apply (apply (ls, tru), nil))

emptyL :: Term
emptyL = apply (apply (pair, nil), nil)

cc :: Term
cc = abstract (\a -> abstract (\b -> let cl = apply (snd, b) in apply (apply (pair, cl), apply (apply (cons, a), cl))))

tail :: Term
tail = abstract (\ls -> apply (fst, apply (apply (ls, cc), emptyL)))

{-

>>> realBool tru
True

>>> realBool fls
False

>>> debug (trueorfalse (churchBool True))
Variable true

>>> debug (trueorfalse (churchBool False))
Variable false

>>> realNat c_0
0

>>> realNat c_1
1

>>> realNat (apply (apply (times, c_2), c_3))
6

>>> realNat (apply (apply (power, c_2), c_3))
8

-}

realBool :: Term -> Bool
realBool t = case debug (apply (apply (t, var "true"), var "false")) of
    Variable "true"  -> True
    Variable "false" -> False
    x                -> error ("realBool, Not a boolean value:" ++ show x)

churchBool :: Bool -> Term
churchBool b = if b then tru else fls

realEq :: Term -> Term -> Bool
realEq a b = case debug (apply (apply (apply (apply (equal, a), b), var "true"), var "false")) of
    Variable "true"  -> True
    Variable "false" -> False
    x                -> error ("realEq, Not a numerical value:" ++ show x)

realNat :: Term -> Int
realNat t = go (debug t) 0
  where
    go a c = case debug (apply (apply (apply (iszro, a), var "true"), var "false")) of
        Variable "true"  -> c
        Variable "false" -> go (debug (apply (prd, a))) (c + 1)
        x                -> error ("realNat, Not a numerical value:" ++ show x)

churchNat :: Int -> Term
churchNat 0 = c_0
churchNat n = apply (scc, churchNat (n - 1))

{-

-- >>> g = abstract (\fct -> abstract (\n -> if realEq n c_0 then c_1 else apply (apply (times, n), apply (fct, apply (prd, n)))))
>>> g = abstract (\fct -> abstract (\n -> apply (apply (apply (apply (equal, n), c_0), c_1), apply (apply (times, n), apply (fct, apply (prd, n))))))
>>> factorial = apply (fix, g)

>>> realNat (apply (factorial, c_0))
1

>>> realNat (apply (factorial, churchNat 1))
1

-- Wow, it takes so long to compute!
>>> realNat (apply (factorial, churchNat 5))
120

>>> sum = abstract (\ls -> apply (apply (ls, plus), c_0))
>>> sums = abstract (\lls -> apply (apply (lls, hole), c_0)) where hole = abstract (\a -> abstract (\b -> apply (apply (plus, b), apply (sum, a))))
>>> l1 = foldr (\a b -> apply (apply (cons, a), b)) nil (churchNat <$> [1..10])
>>> l2 = foldr (\a b -> apply (apply (cons, a), b)) nil ([l1,l1])

>>> realNat (apply (sum, l1))
55

>>> realNat (apply (sum, apply (tail, l1)))
54

>>> realNat (apply (sums, l2))
110

-}

omega :: Term
omega = apply (a, a) where a = abstract (\x -> apply (x, x))

y :: Term
y = abstract (\f -> apply (hole f, hole f)) where hole f = abstract (\x -> apply (f, apply (x, x)))

v :: Term
v = abstract (\f -> apply (hole f, hole f)) where hole f = abstract (\x -> apply (f, abstract (\y -> apply (apply (x, x), y))))

fix :: Term
fix = v

-- | Lambda term, writing from scratch
data Term2 = Variable2 Name
           | Abstraction2 (Name, Term2)
           | Application2 (Term2, Term2)
           deriving Show

prettyTerm2 :: Term2 -> String
prettyTerm2 (Variable2    a     ) = a
prettyTerm2 (Abstraction2 (a, t)) = unpack (format "(λ{}. {})" [a, prettyTerm2 t])
prettyTerm2 (Application2 (a, b)) = unpack (format "{} {}" (prettyTerm2 <$> [a, b]))

{-

>>> showHelper = (error . prettyTerm2) :: Term2 -> ()

>>> fv (Variable2 "a")
fromList ["a"]

>>> fv (Application2 (Variable2 "a", Variable2 "b"))
fromList ["a","b"]

>>> fv (Abstraction2 ("a", Variable2 "a"))
fromList []

>>> fv (Abstraction2 ("a", Variable2 "b"))
fromList ["b"]

>>> subst (Variable2 "a") ("a", Variable2 "b")
Variable2 "b"

>>> subst (Variable2 "a") ("b", Variable2 "b")
Variable2 "a"

>>> showHelper (subst (Abstraction2 ("y", Variable2 "x")) ("x", Abstraction2 ("z", Application2 (Variable2 "z", Variable2 "w"))))
(λy. (λz. z w))

>>> showHelper (subst (Abstraction2 ("x", Variable2 "x")) ("x", Variable2 "y"))
(λx. x)

>>> showHelper (subst (Abstraction2 ("y", Application2 (Variable2 "x", Variable2 "y"))) ("x", Application2 (Variable2 "y", Variable2 "z")))
(λaa. y z aa)

>>> showHelper (evalFull (Variable2 "a"))
a

>>> showHelper (evalFull (Abstraction2 ("x", Variable2 "x")))
(λx. x)

>>> showHelper (evalFull (Application2 (Abstraction2 ("x", Variable2 "x"), Variable2 "y")))
y

>>> showHelper (evalFull (Application2 (Variable2 "x", Variable2 "y")))
x y

>>> id2 = Abstraction2 ("x", Variable2 "x")
>>> showHelper (Application2 (id2, Application2 (id2, Abstraction2 ("z", Application2 (id2, Variable2 "z")))))
(λx. x) (λx. x) (λz. (λx. x) z)

>>> showHelper $ evalFull (Application2 (id2, Application2 (id2, Abstraction2 ("z", Application2 (id2, Variable2 "z")))))
(λz. z)

>>> showHelper $ evalNormal (Application2 (id2, Application2 (id2, Abstraction2 ("z", Application2 (id2, Variable2 "z")))))
(λz. z)

-- evaluation trace
-- (λx. x) (λx. x) (λz. (λx. x) z)
-- (λx. x) (λz. (λx. x) z)
-- (λz. (λx. x) z)
-- (λz. z)

>>> showHelper $ evalCallByName (Application2 (id2, Application2 (id2, Abstraction2 ("z", Application2 (id2, Variable2 "z")))))
(λz. (λx. x) z)

-- evaluation trace
-- (λx. x) (λx. x) (λz. (λx. x) z)
-- (λx. x) (λz. (λx. x) z)
-- (λz. (λx. x) z)

>>> evalLazy (Application2 (id2, Application2 (id2, Abstraction2 ("z", Application2 (id2, Variable2 "z")))))
(Abstraction2 ("z",Application2 (Abstraction2 ("x",Variable2 "x"),Variable2 "z")),fromList [("x",Abstraction2 ("z",Application2 (Abstraction2 ("x",Variable2 "x"),Variable2 "z")))])

-- (λz. (λx. x) z)

-}

fv :: Term2 -> Set Name
fv (Variable2    x     ) = singleton x
fv (Abstraction2 (a, b)) = a `delete` fv b
fv (Application2 (a, b)) = fv a `union` fv b

nextAvailableName :: Name -> Name
nextAvailableName "z" = "aa"
nextAvailableName (splitAt =<< (Prelude.subtract 1 . length) -> (front, Prelude.head -> l)) | l == 'z'  = nextAvailableName front ++ "a"
                                                                                            | otherwise = front ++ [Prelude.succ l]

subst :: Term2 -> (Name, Term2) -> Term2
subst (Application2 (a, b)) t = Application2 (subst a t, subst b t)
subst x@(Abstraction2 (a, b)) t0@(n, t) | a /= n && a `notMember` fv t = Abstraction2 (a, subst b t0)
                                        | a `member` fv t              = subst (Abstraction2 (avoidCapture a, subst b (a, Variable2 (avoidCapture a)))) t0
                                        | otherwise                    = x
  where
    avoidCapture n | n `member` (fv b `union` fv t) = avoidCapture (nextAvailableName n)
                   | otherwise                      = n
subst x@(Variable2 a) (b, t) | a /= b    = x
                             | otherwise = t

-- | eval function, full β-reduction
evalFull :: Term2 -> Term2
evalFull x@(Variable2    _                             ) = x
evalFull (  Abstraction2 (a            , b            )) = Abstraction2 (a, evalFull b)
evalFull (  Application2 (evalFull -> a, evalFull -> b)) = case a of
    Abstraction2 (x, y) -> evalFull (subst y (x, b))
    _                   -> Application2 (a, b)

-- | eval function, normal order (small-step implementation)
evalNormal :: Term2 -> Term2
evalNormal = flip maybe evalNormal <*> go
  where
    go (Variable2    _     ) = Nothing
    go (Application2 (a, b)) = case a of
        Abstraction2 (x, y) -> Just (subst y (x, b))
        x                   -> do
            a' <- go a
            return (Application2 (a', b))
    go (Abstraction2 (a, b)) = do
        b' <- go b
        return (Abstraction2 (a, b'))

-- | eval function, call-by-name (small-step implementation)
evalCallByName :: Term2 -> Term2
evalCallByName = flip maybe evalCallByName <*> go
  where
    go (Variable2    _     ) = Nothing
    go (Application2 (a, b)) = case a of
        Abstraction2 (x, y) -> Just (subst y (x, b))
        x                   -> do
            a' <- go a
            return (Application2 (a', b))
    go (Abstraction2 (a, b)) = Nothing

-- | eval function, lazy evaluation (small-step implementation)
evalLazy :: Term2 -> (Term2, HashMap Name Term2)
evalLazy = flip evalLazy' empty
  where
    evalLazy' x e =
        let (result, sharing) = runState (chainEval x) e
        in  case result of
                Variable2 n -> let st = fromJust (lookup n sharing) in evalLazy' st sharing
                _           -> (result, sharing)
    chainEval = (>>=) . go <*> flip maybe chainEval . return
    go :: Term2 -> State (HashMap Name Term2) (Maybe Term2)
    go (Variable2    _     ) = return Nothing
    go (Application2 (a, b)) = case a of
        Variable2 n -> do
            sharing <- get
            thunk   <- (\x -> maybe (return x) go x) (lookup n sharing)
            when (isJust thunk) (modify (insert n (fromJust thunk)))
            case thunk of
                Just (Abstraction2 (x, y)) -> case b of
                    Variable2 _ -> return (Just (subst y (x, b)))
                    _           -> do
                        modify (insert x b)
                        return (Just y)
                _ -> return Nothing
        Abstraction2 (x, y) -> do
            modify (insert x b)
            return (Just y)
    go (Abstraction2 (a, b)) = return Nothing

type Context = HashMap String Int

data Term3 = Index Int
           | Abstraction3 Term3
           | Application3 Term3 Term3
           deriving Show

prettyTerm3 :: Term3 -> String
prettyTerm3 (Index        i  ) = show i
prettyTerm3 (Abstraction3 t  ) = unpack (format "(λ. {})" [prettyTerm3 t])
prettyTerm3 (Application3 a b) = unpack (format "{} {}" (prettyTerm3 <$> [a, b]))

{-

>>> showHelper = error . prettyTerm3 :: Term3 -> ()
>>> showHelper2 = error . prettyTerm2 :: Term2 -> ()

>>> cxt = fromList (zip (pure <$> ['a'..'z']) [0..]) :: Context

>>> showHelper (removenames (Variable2 "a") cxt)
0

>>> showHelper (removenames (Abstraction2 ("x", Abstraction2 ("y", Application2 (Variable2 "x", Variable2 "y")))) cxt)
(λ. (λ. 1 0))

>>> showHelper (removenames (Abstraction2 ("x", Abstraction2 ("y", Application2 (Variable2 "x", Variable2 "z")))) cxt)
(λ. (λ. 1 25))

>>> showHelper2 (restorenames (removenames (Abstraction2 ("x", Abstraction2 ("y", Application2 (Variable2 "x", Variable2 "y")))) cxt)) :: ()
(λa. (λb. a b))

>>> showHelper (shift 2 0 (Abstraction3 (Abstraction3 (Application3 (Index 1) (Application3 (Index 0) (Index 2))))))
(λ. (λ. 1 0 4))

>>> showHelper (shift 2 0 (Abstraction3 (Application3 (Application3 (Index 0) (Index 1)) (Abstraction3 (Application3 (Application3 (Index 0) (Index 1)) (Index 2))))))
(λ. 0 3 (λ. 0 1 4))

-}

removenames :: Term2 -> Context -> Term3
removenames t cxt = go [] t
  where
    go currentBV (Variable2    n     ) = fromJust (Index <$> (elemIndex n currentBV <|> lookup n cxt))
    go currentBV (Abstraction2 (n, t)) = Abstraction3 (go (n : currentBV) t)
    go currentBV (Application2 (a, b)) = Application3 (go currentBV a) (go currentBV b)

restorenames :: Term3 -> Term2
restorenames = go []
  where
    go currentBV (Index        i) = Variable2 (currentBV !! i)
    go currentBV (Abstraction3 t) = Abstraction2 (n, go (n : currentBV) t)
        where n = if null currentBV then "a" else nextAvailableName (Prelude.head currentBV)
    go currentBV (Application3 a b) = Application2 (go currentBV a, go currentBV b)

shift :: Int -> Int -> Term3 -> Term3
shift distance cutoff (Index        i  ) = Index (if i < cutoff then i else i + distance)
shift distance cutoff (Abstraction3 t  ) = Abstraction3 (shift distance (succ cutoff) t)
shift distance cutoff (Application3 a b) = Application3 (shift distance cutoff a) (shift distance cutoff b)

subst' :: Term3 -> (Int, Term3) -> Term3
subst' (Index k) (j, s) | k == j    = s
                        | otherwise = Index k
subst' (Abstraction3 t1   ) (j, s) = Abstraction3 (subst' t1 (succ j, shift 1 0 s))
subst' (Application3 t1 t2) p      = Application3 (subst' t1 p) (subst' t2 p)

eval :: Term3 -> Term3
eval (Index        x  ) = Index x
eval (Abstraction3 t  ) = Abstraction3 (eval t)
eval (Application3 a b) = eval (shift (-1) 0 (subst' a (0, shift 1 0 b)))
