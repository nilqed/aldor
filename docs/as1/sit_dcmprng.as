------------------------------ sit_dcmprng.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"


define DecomposableRing: Category == CommutativeRing with {
	provablyIrreducible?: % -> Boolean;
	someFactors: % -> List %;
	default {
		someFactors(x:%):List %			== [x];
		provablyIrreducible?(x:%):Boolean	== false;
	}
}
