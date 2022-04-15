------------------------------ sit_ncid.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "algebra"


define NonCommutativeIntegralDomain: Category == Ring with {
	leftExactQuotient: (%, %) -> Partial %;
	rightExactQuotient: (%, %) -> Partial %;
	default { commutative?:Boolean == false }
}
