----------------------------- sit_freelc.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2001
-- Copyright (c) INRIA 2001
-----------------------------------------------------------------------------

#include "algebra"


define FreeLinearCombinationType(R:Join(ArithmeticType, ExpressionType)):
	Category == Join(ExpressionType, LinearCombinationType R) with {
	map: (R -> R) -> % -> %;
	map!: (R -> R) -> % -> %;
	default {
		map!(f:R -> R)(p:%):% == map(f) p;

		if R has Ring then {
			(n:Integer) * (p:%):% == { import from R; n::R * p; }
		}
	}
}
