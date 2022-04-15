------------------------------- sit_euclid.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "algebra"

macro Z == Integer;


define EuclideanDomain: Category == GcdDomain with {
	diophantine: (%, %, %) -> Partial %;
	divide: (%, %) -> (%, %);
	quo: (%, %) -> %;
	rem: (%, %) -> %;
	divide!: (%, %, %) -> (%, %);
	euclid: (%, %) -> %;
	euclid!: (%, %) -> %;
	euclideanSize: % -> Integer;
	extendedEuclidean: (%, %) -> (%, %, %);
	extendedEuclidean: (%, %, %) -> Partial Cross(%, %);
	rationalReconstruction: (%, %, Z, Z) -> Partial Cross(%, %);
	remainder!: (%, %) -> %;
	if % has CopyableType then PrimitiveType;

	default {
		macro copy? == % has CopyableType;
		divide(a:%, b:%):(%, %)		== (a quo b, a rem b);
		euclid!(p:%, q:%):%		== euclid!(p, q, remainder!);
		local div(p:%, q:%, r:%):(%, %)	== divide(p, q);

		-- TEMPORARY: THOSE DEFAULTS SHOULD BE COMMENTED OUT
		-- AS LONG AS THE COMPILER DOES EARLY-BINDING IN OTHER DEFAULTS
		-- divide!(a:%, b:%, q:%):(%, %)	== divide(a, b);
		-- remainder!(a:%, b:%):%		== a rem b;

		-- uses in-place only when % has CopyableType;
		euclid(p:%, q:%):% == {
			copy? => euclid!(copy(p), copy(q), remainder!);
			euclid!(p, q, rem);
		}

		-- uses in-place only when % has CopyableType;
		local halfEuclid0(p:%, q:%):(%, %) == {
			copy? => halfEuclid!(p, copy(q), divide!);
			halfEuclid!(p, q, div);
		}

		-- uses in-place only when % has CopyableType;
		local halfEuclid(p:%, q:%):(%, %) == {
			copy? => halfEuclid!(copy(p), copy(q), divide!);
			halfEuclid!(p, q, div);
		}

		-- solves a x = b mod m, i.e. a x + m y = b
		diophantine(a:%, b:%, m:%):Partial % == {
			assert(~zero? m);
			zero?(b := b rem m) => [0];
			zero?(a := a rem m) => failed;
			(g, c) := halfEuclid0(a, m);
			failed?(u := exactQuotient(b, g)) => u;
			[remainder!(times!(c, retract u), m)];
		}

		-- solves a x + b y = c, guarantees x reduced modulo b
		extendedEuclidean(a:%, b:%, c:%):Partial Cross(%, %) == {
			zero? c => [(0, 0)];
			import from Partial %;
			zero? b => {
				zero? a or failed?(u := exactQuotient(c, a)) =>
					failed;
				[(retract u, 0)];
			}
			zero? a => {
				failed?(u := exactQuotient(c, b)) => failed;
				[(0, retract u)];
			}
			(g, x) := halfEuclid(a, b);
			failed?(u := exactQuotient(c, g)) => failed;
			x := remainder!(times!(x, retract u), b);
			[x, quotient(c - a * x, b)];
		}

		-- returns (g, x, y) where g = gcd(a,b) = a x + b y
		-- guarantees x reduced modulo b
		extendedEuclidean(a:%, b:%):(%, %, %) == {
			zero? b => (a, 1, 0);
			zero? a => (b, 0, 1);
			(g, x) := halfEuclid(a, b);
			x := remainder!(x, b);
			(g, x, quotient(g - a * x, b));
		}

		-- destroys both a and b if div! destroys 1st and last arg
		-- if exported, must handle the case a or b = 1 separately
		local halfEuclid!(a:%, b:%, div!:(%,%,%) -> (%,%)):(%, %) == {
			import from Integer;
			zero? b => (a, 1); zero? a => (b, 1);
			a1:% := 1; b1:% := 0; q:% := 0;
			if euclideanSize a < euclideanSize b then {
				(a, b) := (b, a);
				(a1, b1) := (b1, a1);
			}
			while ~zero? b repeat {
				temp := b;
				(q, b) := div!(a, b, q);
				a := temp;
				temp1 := b1;
				b1 := add!(a1, times!(minus! q, b1));
				a1 := temp1;
			}
			(a, a1);
		}

		-- destroys both p and q if rem! destroys its 1st argument
		-- does not destroy them otherwise
		euclid!(p:%, q:%, rem!:(%, %) -> %):% == {
			import from Integer;
			zero? q => p; zero? p => q;
			one? p or one? q => 1;
			if euclideanSize p < euclideanSize q then (p,q):=(q,p);
			while q ~= 0 repeat {
				temp := q;
				q := rem!(p, q);
				p := temp;
			}
			p;
		}

		rationalReconstruction(u:%,m:%,n:Z,d:Z):Partial Cross(%,%) == {
			copy? => ratRecon!(copy(u),copy(m),n,d,divide!);
			ratRecon!(u, m, n, d, div);
		}

		-- destroys both a and b if div! destroys 1st and last arg
		local ratRecon!(u:%, m:%, n:Z, d:Z, div!:(%,%,%) -> (%,%)):
			Partial Cross(%, %) == {
			assert(n >= 0); assert(d >= 0);
			s0:% := 0; t0:% := 1;
			s1 := m; t1 := u rem m; q:% := 0;
			while (~zero? t1) and n < euclideanSize t1 repeat {
				(q, r1) := div!(s1, t1, q);
				r0 := minus!(s0, times!(q, t0));
				(s0, s1) := (t0, t1);
				(t0, t1) := (r0, r1);
			}
			assert(~zero? t0);
			d < euclideanSize t0 => failed;
			if canonicalUnitNormal? then {	-- normalize denom (t0)
				-- TEMPORARY: CANNOT OVERLOAD (BUG 1272)
				-- (t0, t1) := unitNormal(t0, t1);
				(t0, t1) := unitNormalize(t0, t1);
			}
			[(t1, t0)];
		}
	}
}
