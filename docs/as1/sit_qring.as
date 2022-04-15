------------------------------- sit_qring.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1997
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "algebra"


define RittRing: Category == CharacteristicZero with {
	/: (%, Integer) -> %;
	inv: Integer -> %;
	default {
		(x:%) / (n:Integer):% == x * inv n;
		if % has Field then { inv(n:Integer):% == inv(n::%) }
	}
}
