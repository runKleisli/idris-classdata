-- https://stackoverflow.com/questions/28257620/choosing-a-typeclass-on-construction-of-a-data-type
-- Using Idris 0.9.18.1

module ClassDataSE



----- Common definitions

class Foo a where
	fooval : a

class Bar a where
	barval : a

%case data Operator = Up | Down

total
classChoice : (x : Operator) -> (Type -> Type)
classChoice Up = Foo
classChoice Down = Bar

data Doo : Type where
	Da : Doo

instance [foodoo] Foo Doo where
	fooval = Da

instance Bar Doo where
	barval = Da



----- Solution by wrapping function of class's datatype in constrained function
-- Commenting out the definition of mkChoosy and reproving, there's clearly a problem.
-- I imagine this could hinder arguments about the value of choosier, which doesn't depend on its arguments in as much as each argument is considered two different things.

data Choosy : (op : Operator) -> (a : Type) -> { P : classChoice op a } -> Type where
	Chosen : Choosy op a

choosier : classChoice op a => (op : Operator) -> (a : Type) -> Type
-- For some reason ?instanceChoice doesn't think the argument `op` and `a` are the signature `op` and `a`, so the constraint argument `classChoice op a` is not assumed.
-- choosier op a = Choosy op a {P=?instanceChoice}
choosier = ?mkChoosy

mkChoosy = proof
	intros
	exact (Choosy op a {P=constrarg})

{-
Can't resolve type class classChoice op a

> guess = choosier Up Doo
-}

guess : Type
guess = ?guess'

guess' = proof
  exact (choosier Up Doo)
  exact Up
  exact Doo
  compute
  exact foodoo

guessanon : Type
guessanon = ?guessanon'

{-
(exact a) not needed after compute when (a) is an anonymous instance:

"When checking right hand side of ClassDataSE.guessanon':
INTERNAL ERROR: Nothing to fill in.
This is probably a bug, or a missing error message.
Please consider reporting at https://github.com/idris-lang/Idris-dev/issues"

> guessanon' = proof
> 	exact (choosier Down Doo)
> 	exact Down
> 	exact Doo
> 	compute
> 	exact %instance
-}

guessanon' = proof
	exact (choosier Down Doo)
	exact Down
	exact Doo
	compute



----- Usage of class's datatype as-is

data Choosy2 : (op : Operator) -> (a : Type) -> {inst : classChoice op a} -> Type where
	Chosen2 : Choosy2 op a

knownTypeBar : Type
knownTypeBar = Choosy2 Down Doo {inst=?knownInstBar_pr}

{-
Alternative - (exact %instance) doesn't work in the REPL, only a named instance's name.

> knownInstBar : Bar Doo
> knownInstBar = %instance

> knownInstBar_pr = proof
> 	compute
> 	exact knownInstBar
-}

knownInstBar_pr = proof
	compute
	exact %instance

knownTypeFoo : Type
knownTypeFoo = Choosy2 Up Doo {inst=?knownInstFoo_pr}

knownInstFoo_pr = proof
	compute
	exact foodoo
