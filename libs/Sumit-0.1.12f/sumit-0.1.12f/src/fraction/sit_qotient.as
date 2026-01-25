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
------------------------ sit_qotient.as ---------------------------
-- Copyright (c) Laurent Bernardin 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994
-----------------------------------------------------------------------------

#include "sumit"

macro Z == Integer;

#if ALDOC
\thistype{Fraction}
\History{Laurent Bernardin}{1/12/94}{created}
\History{Manuel Bronstein}{6/6/96}{made auto-normalizing, algos from Knuth}
\Usage{import from \this~R}
\Params{ {\em R} & \astype{GcdDomain} & a gcd domain\\ }
\Descr{
\this~R forms the fraction field of the gcd domain {\em R}. Fractions
are automatically normalized in this field.
}
\begin{exports}
\category{\astype{FractionFieldCategory} R}\\
\end{exports}
#endif

Fraction(R:GcdDomain): FractionFieldCategory R == add {
	Rep == Record(Numer:R, Denom:R);

	local canon?:Boolean		== canonicalUnitNormal?$R;
	local mkquot(a:R, b:R):%	== { import from Rep; per [a, b]; }
	numerator(x:%):R		== { import from Rep; rep(x).Numer; }
	denominator(x:%):R		== { import from Rep; rep(x).Denom; }
	local numden(x:%):(R, R)	== { import from Rep; explode rep x; }
	0:%				== { import from R; mkquot(0, 1); }
	1:%				== { import from R; mkquot(1, 1); }
	coerce(a:R):%			== mkquot(a, 1);
	coerce(a:Z):%			== a::R::%;
	normalize(x:%):%		== x;
	characteristic:Z		== characteristic$R;

	extree(a:%):ExpressionTree == {
		import from R, List ExpressionTree;
		zero? a => extree(0@R);
		tnum := extree numerator a;
		one? denominator a => tnum;
		tden := extree denominator a;
		-- move the minus sign out of the numerator to the front
		negative? tnum => {
			t := ExpressionTreeQuotient [negate tnum, tden];
			ExpressionTreeMinus [t];
		}
		ExpressionTreeQuotient [tnum, tden];
	}

	local canon(n:R, d:R):% == {
		TRACE("qotient::canon: n = ", n);
		TRACE("qotient::canon: d = ", d);
		assert(~zero? d);
		TRACE("qotient::canon: gcd(n, d) = ", gcd(n, d));
		assert(unit? gcd(n, d));
		canon? => {
			-- TEMPORARY: CANNOT OVERLOAD (BUG 1272)
			-- (newd, newn) :=  unitNormal(d, n);
			(newd, newn) :=  unitNormalize(d, n);
			TRACE("qotient::canon: newn = ", newn);
			TRACE("qotient::canon: newd = ", newd);
			TRACE("", "");
			mkquot(newn, newd);
		}
		mkquot(n, d);
	}

	-(x:%):% == {
		import from R;
		(n, d) := numden x;
		zero? n => x;
		mkquot(- n, d);
	}

	(x:%)^(n:Z):% == {
		import from R;
		zero? x or one? x or zero? n => 1;
		one? n => x;
		(u, v) := numden x;
		n < 0 => canon(v^(-n), u^(-n));
		canon(u^n, v^n);
	}

	(x:%) = (y:%):Boolean == {
		import from R;
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
		TRACE("qotient::/: u = ", u);
		TRACE("qotient::/: v = ", v);
		(w, t) := numden y;
		TRACE("qotient::/: w = ", w);
		TRACE("qotient::/: t = ", t);
		crossgcd(u, v, t, w);
	}

	-- computes (u/v) * (w/t) by crossing gcd's
	local crossgcd(u:R, v:R, w:R, t:R):% == {
		zero? u or zero? w => 0;
		assert(unit? gcd(u, v));
		assert(unit? gcd(w, t));
		unit? v => {
			unit? t => canon(u * w, v * t);
			(d, u1, t1) := gcdquo(u, t);
			canon(u1 * w, v * t1);
		}
		(e, v1, w1) := gcdquo(v, w);
		unit? t => canon(u * w1, v1 * t);
		(d, u1, t1) := gcdquo(u, t);
		canon(u1 * w1, v1 * t1);
	}

	inv(a:%):% == {
		(n, d) := numden a;
		canon(d, n);
	}

	(a:R) / (b:R):%	== {
		assert(~zero? b);
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
		unit? v or unit? t => {
			s := { add? => u * t + v * w; u * t - v * w; }
			zero? s => 0;
			canon(s, v * t);
		}
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
---------------------- test sit_qotient.as --------------------------
#include "sumittest"

macro {
	Z   == Integer;
	Q   == Fraction Z;
}

rational():Boolean == {
	import from Z, Q;

	b := h := 0@Z;
	while zero? h repeat h := random()$Z;
	while zero? b repeat b := h * random()$Z;
	a := h * random()$Z;
	g := gcd(a, b);
	x := a / b;
	g * numerator x = a and g * denominator x = b;
}

stdout << "Testing sit__qotient..." << newline;
sumitTest("rational", rational);
stdout << newline;

#endif

