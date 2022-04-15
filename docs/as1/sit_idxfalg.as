----------------------------- sit_idxfalg.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2001
-- Copyright (c) Marc Moreno Maza 2001
-- Copyright (c) INRIA 2001
-- Copyright (c) LIFL 2001
-----------------------------------------------------------------------------

#include "algebra"


define IndexedFreeAlgebra(R:Join(ArithmeticType, ExpressionType),
			E:Join(TotallyOrderedType, ExpressionType)):
	Category == IndexedFreeRRing(R, E) with {};

