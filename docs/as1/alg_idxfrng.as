----------------------------- alg_idxfrng.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2004
-- Copyright (c) Marc Moreno Maza 2004
-- Copyright (c) INRIA 2004
-- Copyright (c) LIFL 2004
-----------------------------------------------------------------------------

#include "algebra"


define IndexedFreeRRing(R:Join(ArithmeticType, ExpressionType),
			E:Join(TotallyOrderedType, ExpressionType)):
	Category == Join(FreeRRing R, IndexedFreeModule(R, E),
			IndexedFreeLinearArithmeticType(R, E));

