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
------------------------ nnquotient.as ---------------------------
#include "sumit"

#if ASDOC
\thistype{NonNormalizingQuotient}
\History{Laurent Bernardin}{1/12/94}{created}
\History{Manuel Bronstein}{16/5/95}
{added automatic normalization for quotients of integer number systems\\
extracted QuotientCategory}
\History{Manuel Bronstein}{21/3/96}{added QuotientFieldCategory}
\Usage{import from \this~R}
\Params{ {\em R} & SumitIntegralDomain & an integral domain\\ }
\Descr{\this~R forms the quotient field of the integral domain {\em R}}
\begin{exports}
\category{QuotientFieldCategory R}\\
\end{exports}
#endif

NonNormalizingQuotient(R: IntegralDomain): QuotientFieldCategory R == add {
	macro Rep == Record(Numerator:R, Denominator:R);
	import from Rep;

	local ordered?:Boolean		== R has Order;
	local gcd?:Boolean		== R has GcdDomain;
	local canon?:Boolean		== canonicalUnitNormal?$R;
	local quot(a:R, b:R):%		== per [a, b];
	0:%				== quot(0, 1);
	1:%				== quot(1, 1);
	coerce(a:R):%			== quot(a, 1);
	numerator(x:%):R		== rep(x).Numerator;
	denominator(x:%):R		== rep(x).Denominator;
	-(a:%):%			== quot(- numerator a, denominator a);
	inv(a:%):%			== quot(denominator a, numerator a);
	(a:%)^(n:Integer):%	== quot(numerator(a)^n, denominator(a)^n);

	(a:R) / (b:R):% == {
		import from Partial R;
		ASSERT(b ~= 0);
		zero? a => 0;
		quot(a, b);
	}

	normalize(a:%):% == {
		import from Partial R;
		n := numerator a;
		d := denominator a;
		ASSERT(~zero? d);
		zero? n => 0;
		~failed?(q := exactQuotient(n, d)) => quot(retract q, 1);
		if gcd? then (g, n, d) := gquo(n, d);
		canon? => {
			(e, u, uinv) := unitNormal d;   -- d = u e
			quot(uinv * n, e);
		}
		ordered? and negative? d => quot(-n, -d);
		quot(n, d);
	}

	if R has Order then { local negative?(a:R):Boolean == a < 0; }
	if R has GcdDomain then { local gquo(a:R,b:R):(R, R, R) == gcdquo(a,b);}
}		

#if SUMITTEST
---------------------- test nnquotient.as --------------------------
#include "sumittest"

macro {
	Z11 == SmallPrimeField 11;
	P   == SparseUnivariatePolynomial(Z11, "x");
	F   == Quotient P;
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

normal():Boolean == {
	import from SingleInteger, Z, P, F;

	getx():P == { import from Z11; monomial(1, 1); }
	x := getx();
	a := 2 * x^2 + x + (3@Z)::P;
	b := x^2 + 2 * x + 1;
	ab := a/b;
	c := 2 * (x + 1);
	d := 3 * x^2 + x + 1;
	cd := c/d;
	p := ab*cd;
	q := normalize p;
	p = q;
}

print << "Testing quotient..." << newline;
sumitTest("rational", rational);
sumitTest("normal", normal);
print << newline;

#endif

