-- ======================================================================
-- This code was written all or part by Dr. Manuel Bronstein from
-- Inria-CAFE project team. After his sudden death on June 6, 2005, Inria
-- decided to publish this code under the CeCILL open source license in
-- memory of Dr. Manuel Bronstein.
-- 
-- This software is governed by the CeCILL license under French law and
-- abiding by the rules of distribution of free software. You can use,
-- modify and/or redistribute the software under the terms of the CeCILL
-- license as circulated by CEA, CNRS and Inria at the following URL :
-- http://www.cecill.info/licences/Licence_CeCILL_V2-en.html
-- 
-- As a counterpart to the access to the source code and rights to copy,
-- modify and redistribute granted by the license, users are provided
-- only with a limited warranty and the software's author, the holder of
-- the economic rights, and the successive licensors have only limited
-- liability.
-- 
-- In this respect, the user's attention is drawn to the risks associated
-- with loading, using, modifying and/or developing or reproducing the
-- software by the user in light of its specific status of free software,
-- that may mean that it is complicated to manipulate, and that also
-- therefore means that it is reserved for developers and experienced
-- professionals having in-depth computer knowledge. Users are therefore
-- encouraged to load and test the software's suitability as regards
-- their requirements in conditions enabling the security of their
-- systems and/or data to be ensured and, more generally, to use and
-- operate it in the same conditions as regards security.
-- 
-- The fact that you are presently reading this means that you have had
-- knowledge of the CeCILL license and that you accept its terms.
-- ======================================================================
-- 
------------------------------  psqrf.as ---------------------------------
--
-- Gcd and squarefree decomposition of polynomials involving one parameter
--

#include "sumit"

macro {
	Z	== Integer;
	Symbol	== String;
	Ra	== DenseUnivariatePolynomial(R, var);
	COND	== AlgebraicCondition(R, var);
	PR	== Product Rax;
}

ParametricUnivariatePolynomialSquareFree(R:Join(SumitField, CharacteristicZero),
	var:Symbol, Rax:UnivariatePolynomialCategory Ra): with {
		gcdCase: (Rax, Rax, c:COND == Always())-> Case(COND, Rax);
		sqfrCase: (Rax, c:COND == Always()) -> Case(COND, PR);
		quotient: (Rax, Rax, COND) -> Rax;
		simplif: (Rax, COND) -> Rax;
		poly: COND -> Ra;
} == add {
	-- ugly hack for now, must fix COND later
	poly(c:COND):Ra == {
		macro REP == Union(zero:Ra, notzero:List Ra);
		import from REP;
		assert(zeroCase? c);
		(c pretend REP).zero;
	}

	-- the implementation in COND is wrong
	local simp(p:Ra, c:COND):Ra == {
		never? c or always? c => p;
		zeroCase? c => p rem poly(c);
		p;
	}

	local inv(p:Ra, c:COND):Ra == {
		import from Partial Ra;
		assert(~zero? p); assert(~always? c); assert(~never? c);
		u := {
			zeroCase? c => diophantine(p, 1, poly c);
			reciprocal p;
		}
		assert(~failed? u);
		retract u;
	}

	-- used for exact division only, returns the quotient
	quotient(p:Rax, q:Rax, c:COND):Rax == {
		import from Z, Ra, Partial Ra;
		assert(~zero? q);
		zero? p => 0;
		always? c => quotient(p, q);
		never? c => p;
		dq := degree q;
		ilq := inv(leadingCoefficient q, c);
		quot:Rax := 0;
		while ~zero? p repeat {
			d := degree p - dq;
			d < 0 => {
				assert(zero? simplif(p, c));
				return quot;
			}
			cf := simp(ilq * leadingCoefficient p, c);
			quot := add!(quot, cf, d);
			p := simplif(p - cf::Rax * monomial(1, d)$Rax * q, c);
		}
		quot;
	}

	simplif(a:Rax, c:COND):Rax == {
		import from Ra;
		p:Rax := 0;
		for term in a repeat {
			(cf, n) := term;
			p := add!(p, simp(cf, c), n);
		}
		p;
	}

	local musser(a:Rax, n:Z, c:COND):Case(COND, PR) == {
		import from PR, If(COND, Rax), Case(COND, Rax), If(COND,PR);
		assert(~zero? a);
		ans:Case(COND, PR) := empty();
		for branch in gcdCase(a, differentiate a, c) repeat {
			g := object branch;		-- gcd(a, a')
			cg := condition branch;
			aa := simplif(a, cg);
			if zero? degree g then
				ans := addNewCase!(ans, [cg, term(aa, n)]);
			else {
				astar := quotient(aa, g, cg);
				for branch0 in gcdCase(astar, g, cg) repeat {
					gstar := object branch0;
					cg0 := condition branch0;
					aastar := simplif(astar, cg0);
					d1 := quotient(aastar, gstar, cg0);
					m:= musser(simplif(g,cg0),next n,cg0);
					for b in m repeat {
						pr := object b;
						cg1 := condition b;
						ans := addNewCase!(ans,
							[cg1, times!(pr,d1,n)]);
					}
				}
			}
		}
		ans;
	}

	sqfrCase(a:Rax, c:COND):Case(COND, PR) == {
		import from Z, Ra, PR, If(COND, PR);
		zero? a => [c, term(a, 1)]::Case(COND, PR);
		ans:Case(COND, PR) := empty();
		(ct, a) := primitive a;
		for g in musser(a, 1, c) repeat {
			pr := object g;
			cg := condition g;
			u := leadingCoefficient quotient(expand pr, a, cg);
			ans := addNewCase!(ans,
					[normalize cg,mult!(pr,simp(u*ct,cg))]);
		}
		ans;
	}

	-- multiplies product by c, look for term of exponent 1
	local mult!(pr:PR, c:Ra):PR == {
		import from Z, Rax;
		ans:PR := 1;
		un?:Boolean := false;
		for term in pr repeat {
			(p, n) := term;
			if n = 1 then {
				ans := times!(ans, c * p, 1);
				un? := true;
			}
			else ans := times!(ans, p, n);
		}
		un? => ans;
		times!(ans, c::Rax, 1);
	}

	local normalize(p:Rax, c:COND):Rax == {
		import from Ra, Partial Ra;
		p := primitivePart simplif(p, c); 
		never? c => p;
		a := leadingCoefficient p;
		zeroCase? c => simplif(inv(a, c) * p, c);
		failed?(u := reciprocal a) => p;
		retract(u) * p;
	}

	local normalize(p:Ra):Ra == {
		import from R;
		zero? p => p;
		inv(leadingCoefficient p) * p;
	}

	local normalize(c:COND):COND == {
		import from Ra;
		always? c or never? c => c;
		zeroCase? c => normalize(poly c) = 0;
		macro REP == Union(zero:Ra, notzero:List Ra);
		import from REP, List Ra;
		l := (c pretend REP).notzero;
		q:Ra := 1;
		for p in l repeat q := q * p;
		normalize(q) ~= 0;
	}

	-- the version in parpol.as uses the wrong simplify
	gcdCase(uin:Rax, vin:Rax, cin:COND):Case(COND, Rax) == {
		import from Integer, Ra, List Rax;
		macro RESUL == Resultant(Ra, Rax); 

		res:Case(COND, Rax) := empty();
		zero? uin => addNewCase!(res, [cin, normalize(vin, cin)]);
		zero? vin => addNewCase!(res, [cin, normalize(uin, cin)]);

		degree(uin) < degree(vin) => gcdCase(vin, uin, cin);

		c   := copy cin;

		never? c => res;

		-- step 1 : preliminary computations

		us := simplif(uin, c);
		vs := simplif(vin, c);

		-- step 2 : investigation of the contents

		(contu,u) := primitive us;
		(contv,v) := primitive vs;
		gc        := gcd(contu, contv);

		(condu0,condu1) := fork!(c,contu);
		(condc,condu)   := fork!(condu0,contv);
		(condv,c)       := fork!(condu1,contv);

		res := addNewCase!(res,[condc,0$Rax]);
		res := addNewCase!(res,[condu,normalize(vs,condu)]);
		res := addNewCase!(res,[condv,normalize(us,condv)]);

		never? c => res;

		-- Step 3 : simple cases

		degree u = 0 or degree v = 0 => addNewCase!(res, [c, 1]);

		-- Step 4 : investigation of the leading coefficients

		delta := gcd( leadingCoefficient u, leadingCoefficient v );
		(c2,c) := fork!(c,delta);

		res := join!( res, gcdCase(us,vs,c2) );
		never? c => res;

		-- Step 5 : investigation of the subresultant chain
		lists := SPRS(u,v)$RESUL;

		-- Step 6 : Final efforts

		for S in lists repeat {
			lcS    := leadingCoefficient S;
			(c,c2) := fork!(c,lcS);
			res    := addNewCase!( res, [c2,normalize(S,c2)] );
			never? c => return res;
		}

		addNewCase!( res, [c,normalize(v,c)] );
	}
}
