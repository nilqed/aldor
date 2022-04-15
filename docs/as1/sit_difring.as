----------------------------- sit_difring.as ----------------------------------
--
-- Differential rings
--
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "algebra"


define DifferentialRing: Category == CommutativeRing with {
	derivation: Derivation %;
	differentiate: % -> %;
	differentiate: (%, Integer) -> %;
	default {
		derivation:Derivation % ==
			derivation((r:%):% +-> differentiate r);

		differentiate(x:%, n:Integer):% == {
			import from Derivation %;
			assert(n >= 0);
			apply(derivation, x, n);
		}
	}
}

