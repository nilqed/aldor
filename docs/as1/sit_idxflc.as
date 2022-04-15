----------------------------- sit_idxflc.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2001
-- Copyright (c) INRIA 2001
-----------------------------------------------------------------------------

#include "algebra"


define IndexedFreeLinearCombinationType(R:Join(ArithmeticType, ExpressionType),
	E: ExpressionType): Category == FreeLinearCombinationType R with {
		add!: (%, R, E) -> %;
		coefficient: (%, E) -> R;
		setCoefficient!: (%, E, R) -> %;
		monomial: E -> %;
		term: (R, E) -> %;
		default {
			add!(p:%, c:R, v:E):%	== add!(p, term(c, v));
			monomial(e:E):%		== term(1$R, e);
		}
}

