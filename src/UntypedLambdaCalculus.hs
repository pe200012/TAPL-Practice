module UntypedLambdaCalculus where

type Name = String

data Term = Variable Name
          | Abstraction (Term -> Term)
          | Application (Term, Term)

instance Show Term where
    show (Variable n) = "Variable " ++ n
    show (Abstraction _) = "Abstraction <opaque>"
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
>>> debug (apply (apply (apply (test,tru),var "a"),var "b"))
Variable a

>>> debug (apply (apply (apply (test,fls),var "a"),var "b"))
Variable b
-}

-- | If-statement
test :: Term
test = abstract (\l -> abstract (\m -> abstract (\n -> apply (apply (l, m), n))))

-- | simple evaluation, without involving variable substitution
debug :: Term -> Term
debug (Variable n) = Variable n
debug (Abstraction f) = Abstraction f
debug (Application (a, b)) = case debug a of
                                Abstraction f -> debug (f b')
                                _             -> Application (a, b')
    where b' = debug b
