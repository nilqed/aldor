----------------------------- sit_idxflar.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2001
-- Copyright (c) INRIA 2001
-----------------------------------------------------------------------------

#include "algebra"


define IndexedFreeLinearArithmeticType(R:Join(ArithmeticType, ExpressionType),
	E: ExpressionType): Category ==
		Join(IndexedFreeLinearCombinationType(R, E),
					FreeLinearArithmeticType R) with {
		add!: (%, R, E, %) -> %;
}

