----------------------------- sit_idxfmod.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2001
-- Copyright (c) Marc Moreno Maza 2001
-- Copyright (c) INRIA 2001
-- Copyright (c) LIFL 2001
-----------------------------------------------------------------------------

#include "algebra"


define IndexedFreeModule(R:Join(ArithmeticType, ExpressionType),
			E:Join(TotallyOrderedType, ExpressionType)): Category ==
	Join(FreeModule R, IndexedFreeLinearCombinationType(R, E)) with {
		if R has HashType and E has HashType then HashType;
		if R has SerializableType and E has SerializableType then _
			SerializableType;
		degree: % -> E;
		trailingDegree: % -> E;
		generator: % -> Generator Cross(R, E);	-- decreasing
		terms: % -> Generator Cross(R, E);	-- increasing
		leadingTerm: % -> (R, E);
		trailingTerm: % -> (R, E);
		leadingMonomial: % -> %;
		trailingMonomial: % -> %;
		default {
			leadingMonomial(p:%):% == {
				zero? p => 0;
				monomial degree p;
			}

			trailingMonomial(p:%):% == {
				zero? p => 0;
				monomial trailingDegree p;
			}
		}
}
