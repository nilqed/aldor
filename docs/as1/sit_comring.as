------------------------------ sit_comring.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "algebra"


define CommutativeRing: Category == Ring with {
	canonicalUnitNormal?: Boolean;
	cutoff: MachineInteger -> MachineInteger;
	reciprocal: % -> Partial %;
	unitNormal: % -> (%, %, %);
	-- TEMPORARY: CANNOT OVERLOAD (BUG 1272)
	-- unitNormal: (%, %) -> (%, %);
	unitNormalize: (%, %) -> (%, %);
	unit?: % -> Boolean;
	default {
		canonicalUnitNormal?:Boolean		== false;
		commutative?:Boolean			== true;
		unitNormal(x:%):(%, %, %)		== (x, 1, 1);
		cutoff(t:MachineInteger):MachineInteger	== -1;

		-- TEMPORARY: CANNOT OVERLOAD (BUG 1272)
		-- unitNormal(x:%, z:%):(%, %) == {
		unitNormalize(x:%, z:%):(%, %) == {
			(y, u, uinv) := unitNormal x;	-- x = u y
			(y, uinv * z);
		}

		unit?(x:%):Boolean == {
			import from Partial %;
			~(zero? x or failed? reciprocal x)
		}
	}
}
