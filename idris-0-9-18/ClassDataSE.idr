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

-- With direct interface
guess' = proof
  exact (Choosy Up Doo {P=foodoo})

{-
-- With wrapper function instead

guess' = proof
  exact (choosier Up Doo)
  exact Up
  exact Doo
  compute
  exact foodoo
-}

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
Alternative - (exact %instance) doesn't work in the REPL, only instance with a name declared.

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



----- Simplify circumstances of not being able to resolve the typeclass

foosyn : Type -> Type
foosyn = Foo

-- if seewhatsinside has two arguments of type `a`, there's the issue.
-- It doesn't, the goal is (Foo a -> a -> b)
checkmeforclues : foosyn a => a -> b
checkmeforclues = ?seewhatsinside

-- No problem, the goal is (Foo a -> a -> Foo a)
checkmeforclues2 : foosyn a => a -> foosyn a
checkmeforclues2 = ?seewhatsinside2

{-
> foosyn2 : Type -> Type
> foosyn2 t = case t of
> 		Nat => Foo t
> 		_ => Bar t

You try and prove lookwhatsinside

> checkmeforcluestoo : foosyn2 a => a -> b
> checkmeforcluestoo = ?lookwhatsinside

and if you apply (compute) you get (case block in foosyn2 a a = Foo a), which looks like a bug.

This won't do the same, for instance:

> bake : Bool -> Bool
> bake t = case t of
> 		False => t
> 		_ => t

> bakeisid : bake t = t
> bakeisid = ?bake_lem
-}



----- More options explored

{-
Successful isolation step in contrast of Choosy3 w/ checkmeforclues:

When checking type of ClassDataSE.Chosen3:
Can't resolve type class foosyn a

> data Choosy3 : foosyn a => (a : Type) -> Type where
> 	Chosen3 : Choosy3 a
-}

{-
-- This doesn't help
> data Choosy4 : (p : foosyn a) => (a : Type) -> Type where
> 	Chosen4 : {a : Type} -> { p' : foosyn a } -> Choosy4 a
-}

-- This also works.
data Choosy5 : (a : Type) -> (p : foosyn a) -> Type where
	Chosen5 : (p' : foosyn a) -> Choosy5 a p'

{-
When checking type of ClassDataSE.Special6:
Choosy6 a constrarg Doo does not have a function type (Type)

data Choosy6 : foosyn a => (a : Type) -> Type where
	Special6 : Choosy6 Doo @{foodoo}
-}



----- A functioning option where a constraint argument appears in the type of (Choosy7).

{-
This works, but passes the same errors from before down the line to declaring the values.

The (<==) is 'match' application, documented in part here:
http://docs.idris-lang.org/en/latest/reference/misc.html
-}
data Choosy7 : (p : foosyn a) => (a : Type) -> Type where
	Chosen7 : Type <== Choosy7

{-
I suspect this is at the heart of the problem.

> Chosen7

(input):Can't infer argument a to Chosen7, 
        Can't infer argument p to Chosen7, 
        Can't infer argument a2 to Chosen7

> Chosen7 {a=Doo}

(input):1:9:a is not an implicit argument of ClassDataSE.Chosen7

> Choosy7 Doo

Can't resolve type class foosyn a

> inspector: Choosy7 Doo

When checking type of ClassDataSE.inspector:
Can't resolve type class foosyn a

That is to say, there is a hole of type (foosyn a) arising from a declaration, rather than a definition, and that hole must be filled for the type to check.

I count the following as a successful proof of (Choosy7 Doo).
Though reported as type (chews), running printdef on (chews) will show (Choosy7 Doo), so it should be recognized as a (Choosy7 Doo) when its type is computed.
-}

inspector: ?chews
inspector = Chosen7

chews = proof
  exact (Choosy7 Doo)
  exact Doo
  compute
  exact foodoo



-- For good measure, an anonymous instance version of a (Choosy7 a) proof
data Dar = Dei

instance Foo Dar where fooval = Dei

inspectorAnon : ?chomps
inspectorAnon = Chosen7

chomps = proof
  exact (Choosy7 Dar)
  exact Dar
  compute
-- Only in REPL, where anonymous instance isn't acknowledged: exact %instance

{-
An alternative proof to chomps:

> chomps = proof
>   exact (Choosy7 Dar)
>   exact Doo
>   compute
>   exact foodoo

It's kind of hard to see whether it makes a difference whether you perform the proof correctly or as just shown.
-}

{-
This (seeker) declared below has a bad value, since the parameters to (Choosy7) are undetermined.

In the alternative proof to (chomps), the goal satisfied by (exact (Choosy7 Dar)) and the mismatching goals that emerge after satisfying it are the same as the assumptions available when defining (seeker) in the REPL, which in turn show the same splitting of one argument into two - the (a : Type) that (seeker) depends on and the (a2 : Type) that (Choosy7 a2) depends on - seen in (mkChoice).

We do not need to make such a proof, and have defined it by the exact constructor. However, the behavior of the proof engine here is very interesting, because it appears an instance of (foosyn a) is accepted as an instance of (foosyn a2).
-}

seeker : Type <== Choosy7
seeker = Chosen7

{-
-- Try defining interactively as if by below to see the assumptions or behavior of the proof engine.

seeker = ?seeker_sat
seeker_sat = proof
  intros
  exact Chosen7
-}



----- One last option

{-
When checking type of ClassDataSE.Chosen8:
Can't resolve type class foosyn a

> data Choosy8 : foosyn a => (a : Type) -> Type where
> 	Chosen8 : foosyn a => Choosy8 a

Still allows bad value by method of (seeker) for Choosy7, but does constrain the circumstances for it.

> data Choosy8 : foosyn a => (a : Type) -> Type where
> 	Chosen8 : foosyn a => Type <== Choosy8
-}
