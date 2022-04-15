----------------------------- sit_freealg.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2001
-- Copyright (c) Marc Moreno Maza 2001
-- Copyright (c) INRIA 2001
-- Copyright (c) LIFL 2001
-----------------------------------------------------------------------------

#include "algebra"


define FreeAlgebra(R:Join(ArithmeticType, ExpressionType)):
	Category == FreeRRing R with {
	if R has Ring then Algebra R
}

