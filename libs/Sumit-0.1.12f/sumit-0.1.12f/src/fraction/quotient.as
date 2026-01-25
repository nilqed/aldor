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
------------------------ quotient.as ---------------------------
#include "sumit"

macro Z == Integer;

#if ASDOC
\thistype{Quotient}
\History{Laurent Bernardin}{1/12/94}{created}
\History{Manuel Bronstein}{6/6/96}{made auto-normalizing, algos from Knuth}
\Usage{import from \this~R}
\Params{ {\em R} & GcdDomain & a gcd domain\\ }
\Descr{
\this~R forms the quotient field of the gcd domain {\em R}. Quotients
are automatically normalized in this field.
}
\begin{exports}
\category{QuotientFieldCategory R}\\
\end{exports}
#endif

Quotient(R: GcdDomain): QuotientFieldCategory R == add {
	macro Rep == Record(Numerator:R, Denominator:R);
	import from Rep;

	-- TEMPORARY: THIS SHOULD COME FROM quotcat BUT DOESN'T (1.1.9)
	sample:%			== sample$R :: %;

	local canon?:Boolean		== canonicalUnitNormal?$R;
	local mkquot(a:R, b:R):%	== per [a, b];
	0:%				== mkquot(0, 1);
	1:%				== mkquot(1, 1);
	coerce(a:R):%			== mkquot(a, 1);
	numerator(x:%):R		== rep(x).Numerator;
	denominator(x:%):R		== rep(x).Denominator;
	local numden(x:%):(R, R)	== explode rep x;
	normalize(x:%):%		== x;

	local canon(n:R, d:R):% == {
		ASSERT(~zero? d);
		canon? => {
			(e, u, uinv) := unitNormal d;	-- d = u e
			mkquot(uinv * n, e);
		}
		mkquot(n, d);
	}

	-(x:%):% == {
		(n, d) := numden x;
		zero? n => x;
		mkquot(- n, d);
	}

	(x:%)^(n:Z):% == {
		zero? x or one? x or zero? n => 1;
		one? n => x;
		(u, v) := numden x;
		n < 0 => canon(v^(-n), u^(-n));
		canon(u^n, v^n);
	}

	(x:%) = (y:%):Boolean == {
		(u, v) := numden x;
		(w, t) := numden y;
		u = w and v = t => true;
		canon? => false;
		u * t = v * w;
	}

	(x:%) * (y:%):% == {
		(u, v) := numden x;
		(w, t) := numden y;
		crossgcd(u, v, w, t);
	}

	(x:%) / (y:%):% == {
		(u, v) := numden x;
		(w, t) := numden y;
		crossgcd(u, v, t, w);
	}

	-- computes (u/v) * (w/t) by crossing gcd's
	local crossgcd(u:R, v:R, w:R, t:R):% == {
		zero? u or zero? w => 0;
		ASSERT(unit? gcd(u, v));
		ASSERT(unit? gcd(w, t));
		(d, u1, t1) := gcdquo(u, t);
		(e, v1, w1) := gcdquo(v, w);
		canon(u1 * w1, v1 * t1);
	}

	inv(a:%):% == {
		(n, d) := numden a;
		canon(d, n);
	}

	(a:R) / (b:R):%	== {
		ASSERT(~zero? b);
		zero? a => 0;
		one? b => a::%;
		(g, a1, b1) := gcdquo(a, b);
		canon(a1, b1);
	}

	(c:R) * (x:%):% == {
		zero? c or zero? x => 0;
		one? c => x;
		(a, b) := numden x;
		(g, c1, b1) := gcdquo(c, b);
		mkquot(c1 * a, b1);
	}

	(x:%) - (y:%):% == {
		zero? x => - y; zero? y => x;
		addsub(x, y, false);
	}

	(x:%) + (y:%):% == {
		zero? x => y; zero? y => x;
		addsub(x, y, true);
	}

	local addsub(x:%, y:%, add?:Boolean):% == {
		(u, v) := numden x;
		(w, t) := numden y;
		(d, v1, t1) := gcdquo(v, t);
		s := { add? => u * t1 + v1 * w; u * t1 - v1 * w; }
		zero? s => 0;
		one? d => canon(s, v * t);
		(e, s1, d1) := gcdquo(s, d);
		canon(s1, v1 * t1 * d1);
	}

	lift(D:Derivation R):Derivation(% pretend Ring) == {
		derivation {(f:%):% +-> {
			(n, d) := numden f;
			dn := D n;
			zero?(dd := D d) => dn / d;
			(g, u, v) := gcdquo(D d, d);	-- d'/d = u/v
			a := v * dn - n * u;		-- f' = a / (d v)
			one? g => mkquot(a, v * d);
			(e, s, t) := gcdquo(a, g);
			canon(s, v * v * t);
		} }
	}
}		

#if SUMITTEST
---------------------- test quotient.as --------------------------
#include "sumittest.as"

macro {
	Z   == Integer;
	Q   == Quotient Z;
}

rational():Boolean == {
	import from Z, Q, RandomNumberGenerator;

	b := h := 0@Z;
	while zero? h repeat h := randomInteger();
	while zero? b repeat b := h * randomInteger();
	a := h * randomInteger();
	g := gcd(a, b);
	x := a / b;
	g * numerator x = a and g * denominator x = b;
}

print << "Testing quotient..." << newline;
sumitTest("rational", rational);
print << newline;

#endif

