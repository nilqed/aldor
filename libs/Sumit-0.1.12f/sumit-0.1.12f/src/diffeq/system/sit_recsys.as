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
------------------------------ sit_recsys.as ------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it ©INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I   == MachineInteger;
	Z   == Integer;
	V   == Vector;
	M   == DenseMatrix;
	PRX == List Cross(RX, Z);
	Rx  == Fraction RX;
	SYS == LinearOrdinaryFirstOrderSystem;
	RXE == LinearOrdinaryRecurrence(R, RX);
	FFX == UnivariateFactorialPolynomial(F, FX);
}

#if ALDOC
\thistype{LinearOrdinaryRecurrenceSystemRationalSolutions}
\History{Manuel Bronstein}{26/9/2000}{created}
\Usage{import from \this(R, F, $\iota$, RX, FX)}
\Params{
{\em R} & \astype{GcdDomain} & The coefficient ring\\
        & \astype{RationalRootRing} &\\
{\em F} & \astype{Field} & A field containing R\\
$\iota$ & $R \to F$ & Injection from R into F\\
{\em RX} & \astype{UnivariatePolynomialCategory} R & Polynomials over R\\
{\em FX} & \astype{UnivariatePolynomialCategory} F & Polynomials over F\\
}
\Descr{\this(R, F, $\iota$, RX, FX) provides a rational solver
for first order systems of linear ordinary recurrence operators
with polynomial coefficients.}
\begin{exports}
\asexp{kernel}: & SYS RX $\to$ (RX, \astype{DenseMatrix} UFP(F, FX)) &
Rational solutions\\
\end{exports}
\begin{aswhere}
SYS &==& \astype{LinearOrdinaryFirstOrderSystem}\\
UFP &==& \astype{UnivariateFactorialPolynomial}\\
\end{aswhere}
#endif

LinearOrdinaryRecurrenceSystemRationalSolutions(
	R:Join(GcdDomain, RationalRootRing),
	F:Field, inj: R -> F,
	RX: UnivariatePolynomialCategory R,
	FX: UnivariatePolynomialCategory F): with {
		kernel: SYS RX -> (RX, M FFX);
#if ALDOC
\aspage{kernel}
\Usage{\name~L}
\Signature{SYS RX}
{(RX, \astype{DenseMatrix} \astype{UnivariateFactorialPolynomial}(F, FX))}
\begin{aswhere}
SYS &==& \astype{LinearOrdinaryFirstOrderSystem}\\
\end{aswhere}
\Params{
{\em L} & \astype{LinearOrdinaryFirstOrderSystem} RX &
A first order recurrence system\\
}
\Retval{Returns $(d, [P_1,\dots,P_m])$ such that $\{P_1/d,\dots,P_m/d\}$ is
a basis for all the rational solutions of $LY = 0$.}
#endif
} == add {
	local delta(p:Rx):Rx == 0;

	local sigma(p:Rx, n:Z):Rx == {
		import from RX;
		zero? n => p;
		m := (-n)::R;
		translate(numerator p, m) / translate(denominator p, m);
	}

	local fact(p:RX, n:Z):RX == {
		import from R;
		assert(n >= 0);
		prod := copy p;
		for i in 1..n repeat {
			p := translate(p, 1);   -- p(x-1);
			prod := times!(prod, p);
		}
		prod;
	}

	local factexpand(p:PRX):RX == {
		u:RX := 1;
		for term in p repeat {
			(c, n) := term;
			u := times!(u, fact(c, n));
		}
		u;
	}

	local trace(L:SYS RX):() == {
		import from ExpressionTree, TextWriter, Character, String;
		import from V RX, M RX;
		(v, m) := matrix L;
		stderr << "recsys::system: lhs = " << newline;
		maple(stderr, extree v);
		stderr << "recsys::system: rhs = " << newline;
		maple(stderr, extree m);
		stderr << newline << newline;
	}

	kernel(L:SYS RX):(RX, M FFX) == {
		import from I, Z, PRX, Automorphism Rx, Rx, V Rx, M Rx,_
			LinearOrdinaryFirstOrderSystemPolynomialSolutions(R,_
							F, inj, RX, RXE, FFX);
		empty?(d := denom L) => (1, kernel L);
		dd := factexpand d;
		TRACE("recsys::kernel: dd = ", dd);
		d1 := inv(dd::Rx);
		t := diagonal [d1 for i in 1..machine order L];
		LL := changeVariable(L, t, morphism sigma, delta);
		(dd, kernel LL);
	}

	-- return [(g1,e1),...,(gk,ek)] where
	-- (g,e) means g \sigma^{-1}(g) ... \sigma^{-e}(g)
	local denom(L:SYS RX):PRX == {
		import from Z, R, V RX, LinearAlgebra(RX, M RX);
		(a, m) := matrix L;
		d := determinant m;
		a0:RX := 1;
		a1 := a0;
		for p in a repeat {
			(g, doverg, ignore) := gcdquo(d, p);
			a0 := lcm(a0, doverg);
			a1 := lcm(a1, p);
		}
		universalBound(translate(a1, 1), a0);
	}
}

#if SUMITTEST
-------------------------   test for recsys.as   -------------------------
#include "sumittest"

macro {
	I == MachineInteger;
	Z == Integer;
	Q == Fraction Z;
	ZX == DenseUnivariatePolynomial Z;
	QX == DenseUnivariatePolynomial Q;
	QFX==UnivariateFactorialPolynomial(Q, QX);
	Zx == Fraction ZX;
	Qx == Fraction QX;
	M == DenseMatrix;
}

-- non-simple example from Abramov & Barkatou, ISSAC'98
local nonsimple():Boolean == {
	import from I, Z, Q, ZX, Zx, QX, Qx, QFX, M QFX;
	import from LinearOrdinaryFirstOrderSystem ZX;
	import from UnivariateFreeFiniteAlgebraOverFraction(Z, ZX, Q, QX);
	import from LinearOrdinaryRecurrenceSystemRationalSolutions(Z, Q,
								coerce, ZX, QX);
	m:M Zx := zero(4, 4);
	x := monom$ZX :: Zx;
	f := 5@Z :: Zx;
	d := x + f;
	m(1, 1) := (x-1)/d;
	m(1, 2) := (x*x*x + 7*x*x + 4*x)/d;
	m(1, 3) := - x - 1;
	m(1, 4) := (1-x)*(x*x + 5*x + f)/d;
	m(2, 1) := (x-1)/(x*(x+1)*d);
	m(2, 2) := x * m(2, 1);
	m(2, 4) := m(2, 2);
	m(3, 1) := m(1, 1);
	m(3, 2) := x * m(3, 1);
	m(3, 3) := -x;
	m(3, 4) := - (x*x*x + 3*x*x - 5*x - f)/d;
	m(4, 1) := -m(1,1)/x;
	m(4, 2) := -m(1,1);
	m(4, 3) := 1;
	m(4, 4) := (x+4@Z::Zx)*m(1,1);
	L := system m;
	(den, num) := kernel L;
	numberOfColumns num ~= 2 => false;
	dden := makeRational den;
	sol:M Zx := zero(4, numberOfColumns num);
	ssol := copy sol;
	for i in 1@I..4 repeat for j in 1..numberOfColumns num repeat {
		p := expand(num(i, j)) / dden;
		(na, np) := makeIntegral numerator p;	-- p = (np/na)/(dp/da)
		(da, dp) := makeIntegral denominator p;	--   = (da np)/(na dp)
		sol(i, j) := (da * np) / (na * dp);
		ssol(i, j) := (da * translate(np,-1)) / (na * translate(dp,-1));
	}
	zero?(ssol - m * sol);
}

-- simple example with 2-dimensional kernel coming from eigenring computation
local simple():Boolean == {
	import from MachineInteger, Z, Q, ZX, Zx, QX, Qx, QFX, M QFX;
	import from LinearOrdinaryFirstOrderSystem ZX;
	import from UnivariateFreeFiniteAlgebraOverFraction(Z, ZX, Q, QX);
	import from LinearOrdinaryRecurrenceSystemRationalSolutions(Z, Q,
								coerce, ZX, QX);
	m:M Zx := zero(4, 4);
	x := monom$ZX :: Zx;
        q := 4*x*x + 2*x - 1;
        d := 2*x*(2*x-1)*(2*x+1)*(2*x+1);
        m(1, 1) := 4*x*x*q / d;
        m(1, 2) := 8*x*x*x / d;
        m(1, 3) := -q / d;
        m(1, 4) := -2*x / d;
        m(2, 1) := 4*x*x / d;
        m(2, 2) := 16*x*x*x*x / d;
        m(2, 3) := -1 / d;
        m(2, 4) := -m(2,1);
        m(3, 1) := -2*x*q / d;
        m(3, 2) := m(2,4);
        m(3, 3) := q*q / d;
        m(3, 4) := -m(3,1);
        m(4, 1) := m(1,4);
        m(4, 2) := -m(1,2);
        m(4, 3) := q / d;
        m(4, 4) := m(1,1);
	L := system m;
	(den, num) := kernel L;
	numberOfColumns num ~= 2 => false;
	dden := makeRational den;
	sol:M Zx := zero(4, numberOfColumns num);
	ssol := copy sol;
	for i in 1@I..4 repeat for j in 1..numberOfColumns num repeat {
		p := expand(num(i, j)) / dden;
		(na, np) := makeIntegral numerator p;	-- p = (np/na)/(dp/da)
		(da, dp) := makeIntegral denominator p;	--   = (da np)/(na dp)
		sol(i, j) := (da * np) / (na * dp);
		ssol(i, j) := (da * translate(np,-1)) / (na * translate(dp,-1));
	}
	zero?(ssol - m * sol);
}

stdout << "Testing sit__recsys..." << endnl;
sumitTest("simple 4th order system", simple);
sumitTest("non-simple 4th order system", nonsimple);
stdout << endnl;

#endif
