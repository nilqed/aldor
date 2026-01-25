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
----------------------------- sit_sup.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{SparseUnivariatePolynomial}
\History{Manuel Bronstein}{20/5/94}{created}
\History{Thom Mulders}{27/5/97}{added partial add!}
\Usage{ import from \this~R\\ import from \this(R, x) }
\Params{
{\em R} & \astype{SumitType} & The coefficient domain\\
        & \astype{ArithmeticType} &\\
{\em x} & \astype{Symbol} & The variable name (optional)\\
}
\Descr{\this(R, x) implements sparse univariate polynomials with coefficients
in R.}
\begin{exports}
\category{\astype{UnivariatePolynomialCategory} R}\\
\end{exports}
#endif

macro Z == Integer;

SparseUnivariatePolynomial(R:Join(ArithmeticType,SumitType),avar:Symbol==new()):
	UnivariatePolynomialCategory R == add {
	macro Term	== UnivariateMonomial(R, avar);
	Rep	== List Term;            -- sorted, highest term first
	import from Term, Rep, R, Z;

	local intdom?:Boolean		== R has IntegralDomain;
	0:%				== per empty;
	1:%				== per [monomial(1, 0)];
	zero?(p:%):Boolean		== empty? rep p;
	reductum(p:%):%			== { zero? p => 0; per rest rep p }
	(x:%) = (y:%):Boolean		== rep x = rep y;
	local minusTerm(t:Term):Term	== monomial(- coefficient t, degree t);
	-(p:%):%			== per(map(minusTerm)(rep p));
	add!(x:%, y:%):%		== per listAdd!(rep x, rep y);
	extree(p:%):ExpressionTree	== p extree avar;
	relativeSize(p:%):MachineInteger== #(rep p);
	generator(p:%):Generator Cross(R, Z)	== gen rep p;
	terms(p:%):Generator Cross(R, Z)	== gen reverse rep p;
	(port:TextWriter) << (p:%):TextWriter	== port(p, avar);

	-- returns all the terms of p of degree stricly less than n
	local trunc(p:%, n:Z):% == {
		while (~zero? p) and degree p >= n repeat p := reductum p;
		p;
	}

	shift!(a:%, n:Z):% == {
		import from Boolean;
		zero? n => a;
		l := rep a;
		assert(~empty? l);
		term := first l;
		(d := n + degree term) < 0 => 0;
		setDegree!(term, d);
		last := l;
		while ~empty?(l := rest l) repeat {
			term := first l;
			(d := n + degree term) < 0 => {
				setRest!(last, empty);
				return a;
			}
			setDegree!(term, d);
			last := l;
		}
		a;
	}

	map!(f:R -> R, p:%):% == {
		import from Boolean;
		l := rep p;
		for term in l repeat map!(f)(term);
		while ~empty?(l) and zero?(coefficient first l) repeat
			l := rest l;
		per l;
	}

	equal?(a:%, b:%, c:%, n:Z):Boolean == {
		n <= 0 => true;
		zero? trunc(trunc(a, n) - trunc(b, n) * trunc(c, n), n);
	}

	copy(p:%):% == {
		zero? p or one? p => p;
		per deepCopy rep p;
	}

	leadingMonomial(p:%):(R, Z) == {
		zero? p => (0, -1);
		(coefficient first rep p, degree first rep p);
	}

	trailingMonomial(p:%):(R, Z) == {
		zero? p => (0, -1);
		while ~zero?(q := reductum p) repeat p := q;
		leadingMonomial p;
	}
		
	local gen(l:List Term):Generator Cross(R, Z) == generate {
		import from Boolean;
		while ~empty? l repeat {
			t := first l;
			l := rest l;
			yield(coefficient t, degree t);
		}
	}

	setCoefficient!(p:%, n:Z, a:R):% == {
		empty?(l := rep p) => monomial(a, n);
		while (d := degree(t := first l)) > n repeat l := rest l;
		d < n => add!(p, a, n);
		setCoefficient!(t, a);
		p;
	}

	if R has RationalRootRing then {
		if R has GcdDomain then {
			macro RR == R pretend Join(RationalRootRing, GcdDomain);
			macro RXY == SparseUnivariatePolynomial %;
			macro SPREAD == UnivariatePolynomialSpread(RR, %, RXY);

			integerDistances(p:%):List Z ==
				integerDistances(p)$SPREAD;

			integerDistances(p:%, q:%):List Z ==
				integerDistances(p, q)$SPREAD;
		}
	}

	if R has FiniteCharacteristic then {
		pthPower(p:%):%	 == per [pthPower t for t in rep p];
		pthPower!(p:%):% == { for t in rep p repeat pthPower! t; p };
	}

	add!(p:%, c:R, n:Z):% == {
		import from Boolean;
		assert(n >= 0);
		zero? c => p;
		zero? p => monomial(c, n);
		p = 1 => add!(monomial(c, n), 1);
		l := rest(s := rep p);
		(d := degree(t := first s)) < n => per cons(monomial(c, n), s);
		d = n => {	-- can have cancellation of leadingCoeff
			zero? setCoefficient!(t, c + coefficient t) => per l;
			p;
		}
		while ~empty?(l) and degree(first l) > n repeat {
			s := l;
			l := rest l
		}
		empty? l or degree(t := first l) < n => {
			setRest!(s, cons(monomial(c, n), l));
			p;
		}
		-- exponent already exists, can have cancellation
		t := first l;
		if zero? setCoefficient!(t, c + coefficient t) then
			setRest!(s, rest l);
		p;
	}

	monomial!(p:%, c:R, n:Z):% == {
		zero? p or p = 1 => monomial(c, n);
		zero? c => 0;
		m := first rep p;
		setCoefficient!(m, c);
		setDegree!(m, n);
		setRest!(rep p, empty);
		p;
	}

	monomial(c:R, n:Z):% == {
		assert(n >= 0);
		zero? c => 0;
		per [monomial(c, n)];
	}

	(c:R) * (p:%):% == {
		zero? c => 0;
		one? c => p;
		l:Rep := empty;
		for t in reverse rep p repeat {
			a := c * coefficient t;
			if intdom? or ~zero?(a) then
				l := cons(monomial(a, degree t), l);
		}
		per l;
	}

	if R has IntegralDomain then {
		times!(c:R, p:%):% == {
			zero? c or zero? p => 0;
			one? c => p;
			one? p => c::%;
			for t in rep p repeat
				setCoefficient!(t, c * coefficient t);
			p;
		}
	}

	(x:%) * (y:%):% == {
		empty?(lx := rep x) or empty?(ly := reverse rep y) => 0;
		z:% := 0;
		for trm in lx repeat {	-- decreasing degrees
			a := coefficient trm; n := degree trm;
			l:Rep := empty;
			for t in ly repeat {	-- increasing degrees
				c := a * coefficient t;
				if intdom? or ~zero?(c) then
					l := cons(monomial(c, n + degree t), l);
			}
			z := add!(z, per l);
		}
		z;
	}

	(x:%) + (y:%):% == {
		zero? x => y; zero? y => x;
		nx := degree(x1 := first(lx := rep x));
		ny := degree(y1 := first(ly := rep y));
		nx > ny => per cons(x1, rep(per(rest lx) + y));
		nx < ny => per cons(y1, rep(x + per rest ly));
		z := per(rest lx) + per(rest ly);
		zero?(c := coefficient x1 + coefficient y1) => z;
		per cons(monomial(c, nx), rep z);
	}

	-- creates new univariate monomials, so that an in-place op later
	-- doesn't affect the copy
	local deepCopy(l:List Term):List Term == {
		c:List Term := empty;
		for t in l repeat c:=cons(monomial(coefficient t,degree t), c);
		reverse! c;
	}

	local deepCopy(d:R, m:Z, l:List Term):List Term == {
		c:List Term := empty;
		for t in l repeat
			c := cons(monomial(d * coefficient t, m + degree t), c);
		reverse! c;
	}

	add!(x:%, d:R, y:%):% == {
		zero? d => x;
		one? d => add!(x, y);
		zero? x => times!(d, copy y);
		one? x => add!(times!(d, copy y), 1);
		per listAdd!(rep x, d, rep y);
	}

	add!(x:%, d:R, h:Z, y:%, n:Z, m:Z):% == {
		zero? d => x;
		per listAdd!(rep x, d, h, rep y, n, m);
	}

#if NONRECURSIVEVERSIONWILLBEDONELATER
	local listAdd!(lx:List Term, ly:List Term):List Term == {
		ans := l := lx; s:List Term := empty;
		while (~empty? lx) and ~(empty? ly) repeat {
			nx := degree(x1 := first lx);
			ny := degree(y1 := first ly);
			if nx > ny then { s := lx; lx := rest lx };
			else {
				ly := rest ly;
				if nx < ny then {
					l := cons(monomial(coefficient y1,
							degree y1), l);
				}
				else {  -- both degrees are equal
					c := coefficient x1 + coefficient y1;
					if zero? c then
						setRest!(s, lx := rest lx);
					else {
						setCoefficient!(x1, c);
						s := lx;
						lx := rest lx;
					}
				}
			}
		}
	}
#endif

	local listAdd!(lx:List Term, ly:List Term):List Term == {
		empty? lx => deepCopy ly; empty? ly => lx;
		nx := degree(x1 := first lx);
		ny := degree(y1 := first ly);
		nx < ny => cons(monomial(coefficient y1, degree y1),
				listAdd!(lx, rest ly));
		nx > ny => { setRest!(lx, listAdd!(rest lx, ly)); lx }
		z := listAdd!(rest lx, rest ly);
		zero?(c := coefficient x1 + coefficient y1) => z;
		setCoefficient!(x1, c);
		setRest!(lx, z);
		lx;
	}

	local listAdd!(lx:List Term, d:R, ly:List Term):List Term == {
		empty? lx => deepCopy(d, 0, ly); empty? ly => lx;
		nx := degree(x1 := first lx);
		ny := degree(y1 := first ly);
		nx < ny => cons(monomial(d * coefficient y1, ny),
				listAdd!(lx, d, rest ly));
		nx > ny => { setRest!(lx, listAdd!(rest lx, d, ly)); lx }
		z := listAdd!(rest lx, d, rest ly);
		zero?(c := coefficient x1 + d * coefficient y1) => z;
		setCoefficient!(x1, c);
		setRest!(lx, z);
		lx;
	}

	local listAdd!(lx:List Term,d:R,h:Z,ly:List Term,n:Z,m:Z):List Term == {
		empty? ly => lx;
		zero? d => lx;
		ny := h + degree(y1 := first ly);
		ny > m => listAdd!(lx, d, h, rest ly, n, m);
		ny < n => lx;
		if ~empty?(lx) then {
			nx := degree(x1 := first lx);
			ny < nx => {
				setRest!(lx, listAdd!(rest lx, d, h, ly, n, m));
				lx;
			}
			ny > nx => cons(monomial(d * coefficient y1, ny),
				listAdd!(lx, d, h, rest ly, n, m));
			z := listAdd!(rest lx, d, h, rest ly, n, m);
			zero?(c := coefficient x1 + d * coefficient y1) => z;
			setCoefficient!(x1, c);
			setRest!(lx, z);
			lx;
		}
		else cons(monomial(d * coefficient y1, ny),
				listAdd!(lx, d, h, rest ly, n, m));			
	}

	coefficient(p:%, n:Z):R == {
		assert(n >= 0);
		for t in rep p repeat {
			n = (e := degree t) => return coefficient t;
			n > e => return 0;
		}
		0;
	}
}

#if SUMITTEST
---------------------- test sup.as --------------------------
#include "sumittest"

macro {
        Z == Integer;
        Zx == SparseUnivariatePolynomial Z;
        Zxt == SparseUnivariatePolynomial Zx;
}

degree():Boolean == {
        import from Z, Zx;
        x := monom;
        p := (x - 1) * (x + 1);
        degree p = 2 and leadingCoefficient p = 1 and zero? p(-1@Z);
}

exactQuotient():Boolean == {
        import from Zx, Partial Zx;

        x := monom;
        a := x - 1;
        b := x + 1;
        p := a * b;
        q := exactQuotient(p, a);	-- must be b
        f := exactQuotient(p, x);	-- must be failed
        ~(failed? q) and failed? f and retract(q) = b;
}

diff():Boolean == {
        import from Z, Zx, Zxt;
        x:Zx := monom;
	t:Zxt := monom;
	p := x * t + (x^2)::Zxt;
	D:Derivation(Zxt) := lift(derivation, t);	-- t' = t
	q := D p;			-- must be (1 + x) t + 2 x
	r := q - p;			-- must be t + 2 x - x^2
	m := x * (x - 2::Zx);
	degree r = 1 and leadingCoefficient r = 1
		and zero?(reductum(r) + m::Zxt);
}

hgcd(a:Zx, b:Zx):Zx == {
	import from Partial Zx, HeuristicGcd(Z, Zx);
	(g, a, b) := heuristicGcd(a, b);
	retract g;
}

mgcd(a:Zx, b:Zx):Zx == {
	import from Partial Zx, ModularUnivariateGcd(Z, Zx);
	stdout << "";	-- THOSE 2 LINES ARE INSERTED TO PREVENT
	(g, a, b) := modularGcd(a, b);
	stdout << "";	-- A (BAD) INLINING OF modularGcd (1.1.12p6)
	retract g;
}

heugcd():Boolean == gcd hgcd;

modgcd():Boolean == gcd mgcd;

gcd(ggt:(Zx,Zx) -> Zx):Boolean == {
	import from Z, Zx;

	x := monom;
	p := x^8 + x^6 - 3*x^4 - 3*x^3 + 8*x^2 +2*x - 5@Z ::Zx;
	q := 3*x^6 + 5*x^4 -4*x^2 -9*x + 21@Z ::Zx;
	r := x^2 + 1;
	g := ggt(p, q);
	rg := ggt(r * p, r * q);
	g = 1 and rg = r;
}

stdout << "Testing sit__sup..." << endnl;
sumitTest("degree", degree);
sumitTest("exactQuotient", exactQuotient);
sumitTest("diff", diff);
sumitTest("heugcd", heugcd);
sumitTest("modgcd", modgcd);
stdout << endnl;
#endif
