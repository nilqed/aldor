----------------------------- sit_froot.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1996
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1996-97
-----------------------------------------------------------------------------

#include "algebra"

macro {
	Z  == Integer;
	RR == FractionalRoot Z;
	GEN== Generator;
}


FractionalRoot(R:CommutativeRing): ExpressionType with {
	integral?: % -> Boolean;
	integralRoot: (R, Z) -> %;
	fractionalRoot: (R, R, Z) -> %;
	integralValue: % -> R;
	multiplicity: % -> Z;
	setMultiplicity!: (%, Z) -> %;
	value: % -> (R, R);
} == add {
	Rep == Record(num:R, den:R, mult:Z);

	import from Z, R, Rep;

	value(r:%):(R, R)		== (numerator r, denominator r);
	integralValue(r:%):R		== { assert(integral? r); numerator r }
	multiplicity(r:%):Z		== rep(r).mult;
	integralRoot(n:R, e:Z):%	== { assert(e > 0); per [n, 1, e] }
	integral?(r:%):Boolean		== one? denominator r;
	local numerator(r:%):R		== rep(r).num;
	local denominator(r:%):R	== rep(r).den;

	if R has Field then {
		fractionalRoot(n:R, d:R, e:Z):% == {
			import from Boolean;
			assert(~zero? d); assert(e > 0);
			per [n/d, 1, e];
		}
	}
	else if R has GcdDomain then {
		fractionalRoot(n:R, d:R, e:Z):% == {
			import from Boolean;
			assert(~zero? d); assert(e > 0);
			zero? n => per [0, 1, e];
			(g, nn, dd) := gcdquo(n, d);
			unit? dd => per [quotient(nn, dd), 1, e];
			per [nn, dd, e];
		}
	}
	else {
		fractionalRoot(n:R, d:R, e:Z):% == {
			import from Boolean, Partial R;
			assert(~zero? d); assert(e > 0);
			zero? n => per [0, 1, e];
			failed?(u := exactQuotient(n, d)) => per [n, d, e];
			per [retract u, 1, e];
		}
	}

	(a:%) = (b:%):Boolean ==
		numerator(a) = numerator(b) and
			denominator(a) = denominator(b) and
				multiplicity(a) = multiplicity(b);

	extree(r:%):ExpressionTree == {
		import from List ExpressionTree;
		ExpressionTreeList [extree value r, extree multiplicity r];
	}

	local extree(n:R, d:R):ExpressionTree == {
		import from List ExpressionTree;
		tnum := extree n;
		one? d => tnum;
		ExpressionTreeQuotient [tnum, extree d];
	}

	setMultiplicity!(r:%, e:Z):% == {
		assert(e > 0);
		rep(r).mult := e;
		r;
	}
}

