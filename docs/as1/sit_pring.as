---------------------- sit_pring.as -----------------------------
--
-- Partial rings, i.e. rings where operations are allowed to fail
--
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "algebra"

macro {
	Z	== Integer;
	U	== Partial %;
}


define PartialRing: Category == ExpressionType with {
	0:%;
	1:%;
	-: % -> U;
	-: (%, %) -> U;
	+: (%, %) -> U;
	*: (%, %) -> U;
	/: (%, %) -> U;
	^: (%, %) -> U;
	<: (%, %) -> U;
	>: (%, %) -> U;
	<=: (%, %) -> U;
	>=: (%, %) -> U;
	coerce: Boolean -> %;
	coerce: Z -> %;
	integer: % -> Partial Z;
	list: List % -> U;
	product: List % -> U;
	sum: List % -> U;
	default {
		0:%			== { import from Z; 0 :: % }
		1:%			== { import from Z; 1 :: % }
		sum(l:List %):U		== partialReduce(+, l, 0);
		product(l:List %):U	== partialReduce(*, l, 1);
		coerce(b?:Boolean):%	== { b? => 1; 0 }
		list(l:List %):U	== failed;

		(a:%) <= (b:%):U == {
			import from Boolean;
			a = b => [true::%];
			a < b;
		}

		(a:%) >= (b:%):U == {
			import from Boolean;
			a = b => [true::%];
			a > b;
		}

		(a:%) > (b:%):U == {
			import from Boolean;
			a = b => [false::%];
			failed?(u := a < b) => u;
			[(0 = retract u)::%];
		}

		-- default is that only the integers are ordered
		(a:%) < (b:%):U == {
			import from Boolean, Z, U, Partial Z;
			a = b => [false::%];
			failed?(u := integer a)
				or failed?(v := integer b) => failed;
			[(retract u < retract v)::%];
		}

		local partialReduce(op: (%, %) -> U, l:List %, def:%):U == {
			import from Boolean;
			empty? l => [def];
			x := first l;
			while ~empty?(l := rest l) repeat {
				failed?(u := op(x, first l)) => return failed;
				x := retract u;
			}
			[x];
		}

		(a:%) - (b:%):U == {
			failed?(u := -b) => u;
			a + retract u;
		}
	}
}
