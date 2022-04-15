------------------------------ sit_mkpring.as ------------------------------
--
-- Turns any ring into a partial ring
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"


MakePartialRing(R:Ring, int:R -> Partial Integer): PartialRing with {
	coerce: R -> %;
	coerce: % -> R;
} == add {
	Rep == R;
	macro U == Partial %;
	import from Rep;

	local field?:Boolean		== R has Field;
	local comring?:Boolean		== R has CommutativeRing;
	0:%				== 0$R :: %;
	1:%				== 1$R :: %;
	coerce(n:Integer):%		== n::R::%;
	coerce(p:R):%			== per p;
	coerce(a:%):R			== rep a;
	- (b:%):U			== [(-(b::R))::%];
	(a:%) + (b:%):U			== [(a::R + b::R)::%];
	(a:%) - (b:%):U			== [(a::R - b::R)::%];
	(a:%) * (b:%):U			== [(a::R * b::R)::%];
	(a:%) = (b:%):Boolean		== a::R = b::R;
	integer(a:%):Partial Integer	== int(a::R);
	extree(a:%):ExpressionTree	== extree(a::R);

	if R has Field then {
		import from R;
		(a:%) / (b:%):U	== [(a::R / b::R)::%];
	}
	else if R has CommutativeRing then {
		(a:%) / (b:%):U	== {
			import from R, Partial R;
			failed?(u := exactQuotient(a::R, b::R)) => failed;
			[retract(u)::%];
		}
	}
	else {
		(a:%) / (b:%):U	== {
			one?(b::R) => [a];
			failed;
		}
	}

	if R has TotallyOrderedType then {
		(a:%) < (b:%):U == {
			import from R;
			[(a::R < b::R)::%];
		}
	}

	(a:%) ^ (b:%):U	== {
		import from Partial Integer;
		failed?(u := integer b) => failed;
		[((a::R)^retract(u))::%];
	}
}
