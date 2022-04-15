------------------------------- sit_intdom.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "algebra"


define IntegralDomain: Category == CommutativeRing with {
	divDiffProd: (%,%,%,%,%) -> %;
	divSumProd: (%,%,%,%,%,%,%) -> %;
	exactQuotient: (%, %) -> Partial %;
	order: % -> % -> Integer;
	orderquo: % -> % -> (Integer, %);
	quotient: (%, %) -> %;
	quotient!: (%, %) -> %;
	quotientBy: % -> (% -> %);
	quotientBy!: % -> (% -> %);
	default {
		reciprocal(x:%):Partial(%)	== exactQuotient(1, x);
		quotient!(x:%, y:%):%		== quotient(x, y);

		order(a:%)(b:%):Integer == {
			(n, c) := orderquo(a)(b);
			n;
		}

		orderquo(a:%)(b:%):(Integer, %) == {
			import from Boolean, Partial %;
			assert(~zero? a and ~zero? b and ~unit? a);
			n:Integer := 0;
			while ~failed?(u := exactQuotient(b, a)) repeat {
				n := next n; b := retract u;
			}
			(n, b);
		}

		quotientBy(l:%):(%->%) == {
			import from Partial %;
			one? l => (a:%):% +-> a;
			failed?(u := reciprocal l) => (a:%):% +-> quotient(a,l);
			retru := retract u;
			(a:%):% +-> retru * a;
		}

		quotientBy!(l:%):(%->%) == {
			import from Partial %;
			one? l => (a:%):% +-> a;
			failed?(u:= reciprocal l) => (a:%):% +-> quotient!(a,l);
			retru := retract u;
			(a:%):% +-> times!(a, retru);
		}

		quotient(x:%, y:%):% == {
			import from Partial %;
			retract exactQuotient(x, y);
		}

		divDiffProd(a1:%, a2:%, b1:%, b2:%, q:%):% ==
			quotient(a1 * a2 - b1 * b2, q);

		divSumProd(a1:%, a2:%, b1:%, b2:%, c1:%, c2:%, q:%):% ==
			quotient(a1 * a2 + b1 * b2 + c1 * c2, q);
	}
}
