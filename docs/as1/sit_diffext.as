----------------------------- sit_diffext.as ----------------------------------
--
-- Differential extensions
--
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "algebra"


define DifferentialExtension(R:CommutativeRing):Category==CommutativeRing with {
	lift: Derivation R -> Derivation %;
	if R has DifferentialRing then DifferentialRing;
	default {
		if R has DifferentialRing then {
			differentiate(x:%):% == {
				import from Derivation %;
				lift(derivation$R) x;
			}
		}
	}
}

