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
----------------------------- sit_spread.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "sumit"

macro {
	Z == Integer;
	ORBIT == Cross(RX, List Z);
}

UnivariatePolynomialSpread(R:Join(RationalRootRing, GcdDomain),
				RX:UnivariatePolynomialCategory R,
				RXY:UnivariatePolynomialCategory RX): with {
	integerDistances: RX -> List Z;
	integerDistances: (RX, RX) -> List Z;
} == add {
	-- the elements of l must all be irreducible
	local orbitalComp(l:List RX):(List RX, RX, List Z) == {
		import from Z, Partial Z;
		p := first l;
		d := degree p;
		assert(d > 0);
		orb:List Z := [0];
		l := rest l;
		ll:List RX := empty;
		for q in l repeat {
			if failed?(s := irrSpread(p, q)) then ll := cons(q, ll);
			else {
				m := retract s;		-- p(n) ~ q(n+m)
				assert(m ~= 0);
				orb := cons(m, orb);
				if m < 0 then {
					p := q;
					orb := [e - m for e in orb];
				}
			}
		}
		(ll, p, orb);
	}

	if R has FactorizationRing then {
		local first(p:RX, e:Z):RX == p;

		-- p must be squarefree already
		local orbitalDecomposition(p:RX):List ORBIT == {
			import from Boolean, Product RX;
			orb:List ORBIT := empty;
			(c, prod) := factor p;
			l:List RX := [first term for term in prod];
			while ~empty? l repeat {
				(l, q, pr) := orbitalComp l;
				orb := cons((q, pr), orb);
			}
			orb;
		}

		integerDistances(p:RX):List Z ==
			spread orbitalDecomposition squareFreePart p;

		integerDistances(p:RX, q:RX):List Z ==
			spread(orbitalDecomposition squareFreePart p,
				orbitalDecomposition squareFreePart q);
	}
	else {
		integerDistances(p:RX):List Z == {
			pp := squareFreePart p;
			spread(pp, pp);
		}

		integerDistances(p:RX, q:RX):List Z ==
			spread(squareFreePart p, squareFreePart q);
	}

	local searchOrbit(b:List ORBIT, p:RX):(MachineInteger, List Z, Z) == {
		import from Boolean, Partial Z, List Z;
		i:MachineInteger := 0;
		for term in b repeat {
			i := next i;
			(q, qorb) := term;
			~failed?(s := irrSpread(p, q)) => {
				m := retract s;		-- p(n) ~ q(n+m)
				return(i, qorb, m);
			}
		}
		(0, empty, 0);
	}

	local spread(l:List Z):Set Z == {
		import from Z;
		spr:Set Z := empty;
		for r in l repeat for rr in l repeat spr := union!(spr, r - rr);
		spr;
	}

	local spread(a:List ORBIT):List Z == {
		import from MachineInteger;
		spr:Set Z := empty;
		for term in a repeat {
			(p, porb) := term;
			spr := union!(spr, spread porb);
		}
		[n for n in spr];
	}

	local spread(la:List Z, lb:List Z, e:Z):Set Z == {
		spr:Set Z := empty;
		for a in la repeat for b in lb repeat
			spr := union!(spr, a - b + e);
		spr;
	}

	local spread(a:List ORBIT, b:List ORBIT):List Z == {
		import from MachineInteger;
		spr:Set Z := empty;
		for term in a repeat {
			(p, porb) := term;
			(bpos, qorb, e) := searchOrbit(b, p);
			if bpos > 0 then {
				spr := union!(spr, spread(porb, qorb, e));
				empty?(b := delete!(b, bpos)) =>
					return [n for n in spr];
			}
		}
		[n for n in spr];
	}

	-- one-candidate version, use when p and q are known to be irreducible
	local irrSpread(p:RX, q:RX):Partial Z == {
		import from Boolean, Z, R, Partial R;
		assert(~zero? p); assert(~zero? q);
		assert(degree p > 0); assert(degree q > 0);
		(d := degree p) ~= degree q => failed;
		d1 := prev d;
		lp := leadingCoefficient p;
		lq := leadingCoefficient q;
		x:RX := monom;
		failed?(u := exactQuotient(lq, lp)) => {
			failed?(u := exactQuotient(lp, lq)) => failed;
			alpha := retract u;
			failed?(u := exactQuotient(coefficient(p, d1)
				- alpha * coefficient(q,d1), d::R * alpha * lq))
					=> failed;
			failed?(mz := integer(RX)(m := retract u)) => failed;
			zero?(alpha * q(x + m::RX) - p) => mz;
			failed;
		}
		alpha := retract u;
		failed?(u := exactQuotient(alpha * coefficient(p, d1)
				- coefficient(q, d1), d::R * lq)) => failed;
		failed?(mz := integer(RX)(m := retract u)) => failed;
		zero?(q(x + m::RX) - alpha * p) => mz;
		failed;
	}

	-- resultant version, use when p and q are not known to be irreducible
	local spread(p:RX, q:RX):List Z == {
		import from Boolean, Z, RXY;
		import from FractionalRoot Z, List FractionalRoot Z;
		import from UnivariateFreeFiniteAlgebra2(R, RX, RX, RXY);
		assert(~zero? p); assert(~zero? q);
		f:RX -> RXY := map((c:R):RX +-> c::RX);
		xpm := monom$RXY + (monom$RX)::RXY;
		r := resultant(f p, compose(f q, xpm));
		[integralValue rt for rt in integerRoots(r)$RX]
	}
}
