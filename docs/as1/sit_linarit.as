-------------------------- sit_linarith.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"


define LinearArithmeticType(R:Join(AdditiveType, ExpressionType)): Category ==
	Join(ArithmeticType, ExpressionType, LinearCombinationType R) with {
		^: (%, Integer) -> %;
		coerce: R -> %;

	default {
		coerce(r:R):% == r * 1;

		(p:%) ^ (n:Integer):% == {
			import from BinaryPowering(%, Integer);
			assert(n >= 0);
			binaryExponentiation(p, n);
		}

		if R has Ring then {
			(n:Integer) * (p:%):% == { import from R; n::R * p; }
		}
	}
}
