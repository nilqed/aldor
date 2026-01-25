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
------------------------- order2modp.as --------------------------
#include "sumit"

#if ASDOC
\thistype{ModularSecondOrderLODOFactorizer}
\History{Manuel Bronstein}{16/12/97}{created}
\Usage{import from \this(R, Rx, Rxd)}
\Params{
{\em R} & PrimeFieldCategory & A prime field of odd characteristic\\
{\em Rx} & UnivariatePolynomialCategory R & Coefficients of the operators\\
{\rm Rxd} & LODO Quotient Rx & The differential operators\\
}
\begin{aswhere}
LODO &==& LinearOrdinaryDifferentialOperatorCategory\\
\end{aswhere}
\Descr{\this(R, Rx, Rxd) provides tools for factoring second order
linear ordinary differential equations in $R(x)[\frac d{dx}]$.}
\begin{exports}
factor: & Rxd $\to$ List List Rxd & Factor an operator\\
\end{exports}
#endif

macro {
	I	== SingleInteger;
	Z	== Integer;
	Rx	== Quotient RX;
	M	== DenseMatrix;
}

ModularSecondOrderLODOFactorizer(R:PrimeFieldCategory,
			RX:UnivariatePolynomialCategory R,
			Rxd:LinearOrdinaryDifferentialOperatorCategory Rx):with{
		factor: Rxd -> List List Rxd;
#if ASDOC
\aspage{factor}
\Usage{\name~L}
\Signature{Rxd}{List List Rxd}
\Params{ {\em L} & Rxd & A second order differential operator\\ }
\Retval{
\name(L) returns $[[L]]$ if $L$ is irreducible in $R(x)[d/dx]$,
$[[L_1,R_1]]$ or $[[L_1,R_1],[L_2,R_2]]$ if $L$ has one or two factorizations
into linears,
and an empty list if the $p$-curvature of $L$ is $0$, in
which case $L$ has a fundamental matrix in $R(x)$ and
infinitely many factorizations into linears.}
#endif
} == {
	import from Z;
	ASSERT(characteristic$R > 2);

	add {
	local apply(d:Derivation Rx, q:RX):RX == {
		import from Rx;
		numerator d(q::Rx);
	}

	factor(L:Rxd):List List Rxd == {
		import from R, Rx, List Rx, Partial List Rx, List Rxd;
		import from Derivation Rx;
		ASSERT(degree L = 2);
		TRACE("order2modp::factor, L = ", L);
		TRACE("characteristic = ", characteristic$R);
		-- the transformed equation of a2 y'' + a1 y' + a0 y
		-- through  z = exp(int(a1/a2)/2) y
		-- is z'' - r z, where
		-- r = a1'/(2 a2) - a0/a2 - a1 (2 a2' - a1)/(4 a2^2)
		d := derivation$Rxd;
		a0 := coefficient(L, 0);
		a1 := coefficient(L, 1);
		a2 := leadingCoefficient L;
		two := (2@Z)::Rx;
		a22 := two * a2;
		r := d(a1)/a22 - a0/a2 - a1*(two * d a2 - a1)/a22^2;
		failed?(u := factor(r, d)) => empty();
		empty?(l := retract u) => [[L]];
		TRACE("factors ", "found");
		beta := a1 / two;
		ba := beta / a2;
		[[monomial(a2, 1) + (beta + a2 * v)::Rxd,
			monom + (ba - v)::Rxd] for v in l];
	}

	-- uses the formulas in Mulder's note to compute f modulo a pth-power
	local monomPowRem(n:Z, r:Rx, d:Derivation Rx):RX == {
		ASSERT(n > 2); ASSERT(odd? n);
		import from RX, Product RX;
		dtilde:RX := 1;
		dbar:RX := 1;
		d1:RX := 1;
		d2:RX := 1;
		(dummy, prod) := squareFree(dd:= denominator r);
		for term in prod repeat {
			(q, m) := term;
			ASSERT(m > 0);
			if one? m then dtilde := q;
			else {		-- multiple factor
				dbar := times!(dbar, q);
				d2 := times!(d2, q^(m quo 2));
				if odd? m then d1 := times!(d1, q);
			}
		}
		dhat := quotient(dd, dtilde);
		ddhat := d dhat;
		ddtilde := d dtilde;
		x1 := dtilde * dbar;
		x2 := dbar * ddtilde;
		x3 := quotient(x1 * ddhat, dhat);
		x4 := quotient(dd, dbar);
		x5 := quotient(dhat * ddtilde, dbar);
		x6 := quotient(x4 * d dbar, dbar);
		x7 := quotient(dtilde * ddhat, dbar);
		a:RX := 1;
		b:RX := 0;
		nn := numerator r;
		local c1,c2:RX;
		for i in 1..prev n repeat {
			an := a * nn;
			bd := b * dtilde;
			da := d a;
			db := d b;
			c1 := i * x2 + (i quo 2) * x3;
			c2 := i * x5 + x6 + (prev(i) quo 2) * x7;
			if odd? i then
				(a,b) := (x1*da - c1*a + bd, x4*db - c2*b + an);
			else
				(a,b) := (x4*da - c2*a + bd, x1*db - c1*b + an);
		}
		a * d1^(next(n) quo 2) * d2;
	}

	-- factors D^2-r as (D+u)(D-u), returns the list of u's
	local factor(r:Rx, d:Derivation Rx):Partial List Rx == {
		import from I, R, RX, Rxd, Partial Rx, List Rx;
		-- normally f is the coefficient of D in the
		-- right-remainder of D^p by D^2 - r,
		-- for this particular division, the coefficient of D
		-- in the left-remainder remains the same (use adjoints)
		-- and is quite more efficient to compute than the
		-- right-remainder (it's also more efficient than
		-- computing the p-curvature in matrix form)
		START__TIME;
		f := monomPowRem(characteristic$R, r, d);
		TIME("order2modp::factor: p-curvature at ");
		zero? f => failed;
		-- zero?(f := monomPowRem(characteristic$R, r, d)) => failed;
		df := differentiate f;
		ddf := differentiate df;
		f2 := ((2@Z)::RX * f)::Rx;
		det := r + (df::Rx / f2)^2 - ddf::Rx / f2;
		TIME("order2modp::factor: Delta at ");
		u := sqrt det;
		TIME("order2modp::factor: sqrt(Delta) at ");
		failed? u => [empty()];
		-- failed?(u := sqrt det) => [empty()];
		g := df::Rx / f2;
		TIME("order2modp::factor: g at ");
		zero?(sqrd := retract u) => [[g]];
		[[g + sqrd, g - sqrd]];
	}

	local sqrt(f:Rx):Partial Rx == {
		import from Partial RX;
		zero? f => [0];
		failed?(u := sqrt numerator f) or
			failed?(v := sqrt denominator f) => failed;
		[retract(u) / retract(v)];
	}

	local sqrt(p:RX):Partial RX == {
		import from R, Partial R, Product RX, Partial Product RX;
		ASSERT(~zero? p);
		(c, prod) := squareFree p;
		failed?(u := sqrt prod) or failed?(v := sqrt c) => failed;
		[retract(v) * expand retract u];
	}

	local sqrt(p:Product RX):Partial Product RX == {
		s:Product RX := 1;
		for trm in p repeat {
			(c, n) := trm;
			odd? n => return failed;
			s := times!(s, c, n quo 2);
		}
		[s];
	}

	local sqrt(c:R):Partial R == {
		import from RX, List Cross(R, Z);
		empty?(l := roots(RX)(monomial(1, 2) - c::RX)) => failed;
		(s, n) := first l;
		[s];
	}
	}
}

#if SUMITTEST
-------------------------- test order2modp.as --------------------------
#include "sumittest"

macro {
	I   == SingleInteger;
	Z   == Integer;
	F   == ZechPrimeField p;
	FX  == DenseUnivariatePolynomial F;
	Fx  == Quotient FX;
	Fxd == LinearOrdinaryDifferentialOperator Fx;
}

-- must pass a prime for which D^2-x is irreducible
local airy(p:I):Boolean == {
	import from Z, F, FX, Fx, Fxd, List Fxd, List List Fxd;
	import from ModularSecondOrderLODOFactorizer(F, FX, Fxd);
	x:FX := monom;
	D:Fxd := monom;
	L := D^2 - x::Fx::Fxd;
	l := factor L;
	~empty?(l) and empty?(rest l) and first(first l) = L;
}

local airy():Boolean == {
	import from I;
	airy(3) and airy(5) and airy(7) and airy(11) and airy(13);
}

local kamke(p:I, zerocurv?:Boolean):Boolean == {
	import from Z, F, FX, Fx, Fxd, List Fxd, List List Fxd;
	import from ModularSecondOrderLODOFactorizer(F, FX, Fxd);
	x:FX := monom;
	D:Fxd := monom;
	L := (x^4 + x)::Fx * D^2 + (x^3 - 1)::Fx * D - (x^2)::Fx::Fxd;
	l := factor L;
	empty? l => zerocurv?;
	for lf in l repeat {
		P:Fxd := 1;
		for f in lf repeat P := P * f;
		~zero?(L - P) => return false;
	}
	true;
}

local kamke():Boolean == {
	import from I;
	kamke(3, false) and kamke(5, false) and kamke(7, true)
		and kamke(11, false) and kamke(13, true);
}

print << "Testing second order factorization in Fp[x,d/dx]..." << newline;
sumitTest("Airy", airy);
sumitTest("Kamke", kamke);
print << newline;
#endif

