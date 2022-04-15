------------------------------- alg_ffield.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "algebra"


define FiniteField:Category == Join(Field,FiniteCharacteristic,FiniteSet) with {
	degree: Integer;
	pthRoot: % -> %;
	pthRoot!: % -> %;
	default {

		(a:%)^(n:Integer):% == {
			import from PthPowering %;
			n > 0 => pExponentiation(a, n);
			inv pExponentiation(a, -n);
		}

		-- if size is p^d, then (x^(p^(d-1)))^p = x
		pthRoot(x:%):% == {
			import from Integer;
			% has CopyableType => {
				one? degree => x;
				pthRoot!(copy(x));
			}
			for i in 1..prev(degree) repeat x := pthPower! x;
			x;
		}

		-- if size is p^d, then (x^(p^(d-1)))^p = x
		pthRoot!(x:%):% == {
			import from Integer;
			for i in 1..prev(degree) repeat x := pthPower! x;
			x;
		}
	}
}

