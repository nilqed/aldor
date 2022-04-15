------------------------------- sit_gcd.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "algebra"


define GcdDomain: Category == IntegralDomain with {
	gcd: (%, %) -> %;
	gcd!: (%, %) -> %;
	gcd: Generator % -> %;
	lcm: (%, %) -> %;
	lcm: List % -> %;
	gcdquo: (%, %) -> (%, %, %);
	gcdquo: List % -> (%, List %);
	default {
		gcd!(a:%, b:%):% == gcd(a, b);

		lcm(a:%, b:%):% == {
			(g, aa, bb) := gcdquo(a, b);
			aa * b;
		}

		-- note: lcm/l * gcd/l is NOT always  */l if #l > 2
		-- however, lcm(a_1,...,a_n) = g lcm(b_1,...,b_n)
		-- where g = gcd(a_1,...,a_n) and b_i = a_i / g
		-- uses iterative lcm for the b_i's
		lcm(l:List %):%	== {
			import from Boolean;
			empty? l => 1;
			empty? rest l => first l;
			empty? rest rest l => lcm(first l, first rest l);
			(g, quotients) := gcdquo l;
			m := first quotients;
			while ~empty?(quotients := rest quotients) repeat
				m := lcm(m, first quotients);
			g * m;
		}

		-- default is compute the gcd, then divide
		-- some gcd algorithms yield the cofactors (e.g. modgcd/heugcd)
		gcdquo(a:%, b:%):(%, %, %) == {
			unit?(g := gcd(a, b)) => (1, a, b);
			(g, quotient(a, g), quotient(b, g));
		}

		gcdquo(l:List %):(%, List %) == {
			unit?(g := gcd generator l) => (1, l);
			(g, [quotient(a, g) for a in l]);
		}

		-- default is iterative gcd
		-- must be coded specially where faster is possible (e.g. K[X])
		gcd(l:Generator %):% == {
			g := 0;
			for x in l repeat {
				g := gcd(g, x);
				unit? g => return 1;
			}
			g;
		}
	}
}
