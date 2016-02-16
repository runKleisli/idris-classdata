module ClassDataEx



||| An arbitrary demonstration type.
|||
||| Running apropos on Doo will show you which classes it has instances of.
||| Note the presence of an instance of Fee and Bai, though def.d w/in a function body.
||| This is not the intended result, but it will do for this example.
||| On the upside, those names are not put in the module namespace.
||| Perhaps the instances can be erased?
|||
data Doo = Da



||| A class declaration generates a datatype by that name,
||| seen from running printdef on the class name in the REPL.
||| We ask how far that lets you go towards using instances as values.
||| We deal with the problem of calling member functions like by getfoo.
|||
class Foo a where
	fooval : a

||| Applies this member function of this class to a value of the datatype for the class.
|||
{- The (with) keyword here is a disambiguator.
It is covered in the documentation under Miscellaneous at
	http://docs.idris-lang.org/en/latest/reference/misc.html
Coverage suitable for the Modules & Namespaces Ch. of the Tutorial?
-}
getfoo : Foo a -> a
getfoo x = with x fooval



||| Same as Foo, but with an independent type for the method.
||| We construct a value of type (Bar a) for some (a),
||| so that it can have functions of (Bar a) applied to it.
||| 
class Bar a where
	barval : Nat

{-
Error:

	When checking right hand side of getbar:
	Can't resolve type class Bar a

Why an error here and not with getfoo?


getbar : Bar a -> Nat
getbar x = with x barval
-}

getbar : Bar a -> Nat
getbar x = ?getbar'

getbar' = proof
  intro a
  intro bara
  exact (with bara barval)
  exact a
  exact bara

{-
These don't work, Bar isn't the name of the constructor of a (Bar x).
You see this constructor registered when you print the definition of Bar.

mkBar : Bar Doo
mkBar = ?mkBar'

> mkBar = Bar barval

> mkBar = Bar Z

> mkBar = _ Z

Not this either:

> mkBar : Bar Doo where barval = Z

If it's impossible to implement this variable instance, but named terms are needed, it would be better to switch to record types, such as a built-in option or Vinyl records.

This blog post speaks as if this constructor were real and called instanceC for class C:

https://edwinb.wordpress.com/2011/11/09/type-classes-in-idris/

The Idris tutorial says some helpful things.

It may also be possible to use the Elab shell to fill the hole, but I don't know that for sure.
-}

instance [mkBar] Bar Doo where
	barval = Z

getbarDoo : Nat
getbarDoo = getbar mkBar



||| The Idris tutorial's section on Named Instances tells us
||| we can write: instance [?inst] ?C Doo; ?memberC @{inst}.
||| (?memberC @{inst}) equals (with inst ?memberC) where compile & used here.
|||
class Baez a where
	baezval : Nat

instance [mkBaez] Baez Doo where
	baezval = Z

getbaezDoo : Nat
getbaezDoo = baezval @{mkBaez}



||| Since Idris is liberal with what you can declare within a function body,
||| for Fee we construct the instance of the class so.
||| Since the instance being referred to now depends on the computation,
||| yet member functions of the class can be called on it, our goal looks solved.
|||
class Fee a where
	feeval : Nat

getfeeDoo : Nat
getfeeDoo = feeval @{mkFee}
	where
		instance [mkFee] Fee Doo where
			feeval = Z



||| Same as Fee but with implementation by a function of instances like getfoo is.
|||
class Bai a where
	baival : a

getbai : Bai a -> a
getbai x = baival @{x}

getbaiDoo : Doo
getbaiDoo = getbai mkBai
	where
		instance [mkBai] Bai Doo where
			baival = Da



||| Anonymous instances
||| using Doc's Miscellaneous - Existence of an instance.
|||
class Bau a where
	bauval : a

getbauDoo : Doo
getbauDoo = getbau %instance
	where
		getbau : Bau a -> a
		getbau x = bauval @{x}
		instance Bau Doo where
			bauval = Da



||| Anonymous instances with ambiguous type.
|||
class Fju a where
	fjuval : Nat

getfjuDoo : Nat
getfjuDoo = the (Fju Doo -> Nat) getfju %instance
	where
		getfju : Fju a -> Nat
		getfju x = fjuval @{x}
		instance Fju Doo where
			fjuval = Z



||| Parametric instances phase 1
|||
class Beh a where
	behval : a

data Lift : (a : t) -> Type where
	HasLift : Lift a

{-
This also works

> getbehval = the (Beh (Lift Da) -> Lift Da) getbeh %instance

but only if you make the instance of Beh anonymous (delete [mkBeh])
-}
getbehval : Lift Da
getbehval = getbeh mkBeh
	where
		getbeh : Beh a -> a
		getbeh x = behval @{x}
		instance [mkBeh] Beh (Lift Da) where
			behval = HasLift



||| Parametric instances phase 2
|||
class Beu a where
	beuval : a

-- Where block scoping this doesn't affect getbeuval(1..3)
getbeu : Beu a -> a
getbeu x = beuval @{x}

data Lifty : (a : t) -> Type where
	HasLifty : Lifty a

getclval : (x : Doo) -> Beu (Lifty x)
getclval x = mkBeu
	where
		-- > the (Beu (Lifty Da)) mkBeu : Beu (Lifty Da)
		-- > mkBeu {x=Da}
		instance [mkBeu] Beu (Lifty x) where
			beuval = HasLifty

getbeuval1 : (dar : Doo) -> Lifty dar
getbeuval1 dar = getbeu (getclval dar)

getbeuval2 : (dar : Doo) -> Lifty dar
getbeuval2 dar = getbeu (mkBeu {x=dar})

getbeuval3 : (dar : Doo) -> Lifty dar
getbeuval3 dar = getbeu (with dar mkBeu)



||| Parametric anonymous instances phase 1
|||
class Foi a where
	foival : a

getfoi : Foi a -> a
getfoi x = foival @{x}

data Liftful : (a : t) -> Type where
	HasLiftful : Liftful a

getfoiinst : (x : Doo) -> Foi (Liftful x)
getfoiinst x = %instance
	where
		instance Foi (Liftful x) where
			foival = HasLiftful

getfoival : (dar : Doo) -> Liftful dar
getfoival dar = getfoi (getfoiinst dar)



||| Parametric anonymous instances phase 2
|||
class Bua a where
	buaval : a

getbua : Bua a -> a
getbua x = buaval @{x}

data Liftish : (a : t) -> Type where
	HasLiftish : Liftish a

getbuainst : (x : t) -> Bua (Liftish x)
getbuainst x = %instance
	where
		instance Bua (Liftish x) where
			buaval = HasLiftish

getbuaval : (x : t) -> Liftish x
getbuaval x = getbua (getbuainst x)



||| Parametric anonymous instances phase 3
|||
class Fizfyz a where
	fizfyzval : Nat

getfizfyz : Fizfyz a -> Nat
getfizfyz x = fizfyzval @{x}

data Liftsome : (a : t) -> Type where
	HasLiftsome : Liftsome a

getfizfyzinst : (x : t) -> Fizfyz (Liftsome x)
getfizfyzinst x = %instance
	where
		instance Fizfyz (Liftsome x) where
			fizfyzval = Z

getfizfyzval : (x : t) -> Nat
getfizfyzval x = getfizfyz (getfizfyzinst x)
