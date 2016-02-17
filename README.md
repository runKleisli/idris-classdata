# idris-classdata

Using type classes like data types.

In Idris, on defining every class, a like `Type->Type` is created. Its application to a value can be treated as the constraint that that value have an instance of the class, or as a type whose inhabitants are instances of the class for that value.

Simple computations of class constraints and instances allow you to mimic some of the functionality of data types by passing around class constraints and instances as values.

* ClassDataEx.idr focuses on showing how instances are computed by gradually introducing relevant pieces of the language until it's clear how to specify a function taking a value and returning an instance of a class dependent on that value and where the instance's members are defined in terms of that value.

* ClassDataSE.idr focuses on showing how classes are computed by addressing a StackExchange question regarding a problem arising from specifying an instance must exist in the traditional way, through type class constraints rather than an instance-valued function argument, when using a class-valued function which has multiple cases in the definition, and hence which in the expression where it's applied to variable arguments is not syntactically equal to the type it computes for any given input case.
