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
------------------------------ sit_recrat.as ------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it ©INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	Z   == Integer;
	V   == Vector;
	PRX == List Cross(RX, Z);
	Rx  == Fraction RX;
	RxE == LinearOrdinaryRecurrenceQ(R, RX);
	FFX == UnivariateFactorialPolynomial(F, FX);
	PFX == Partial FFX;
}

#if ALDOC
\thistype{LinearOrdinaryRecurrenceRationalSolutions}
\History{Manuel Bronstein}{27/7/2000}{created}
\Usage{import from \this(R, F, $\iota$, RX, RXE, FX)}
\Params{
{\em R} & \astype{GcdDomain} & The coefficient ring\\
        & \astype{RationalRootRing} &\\
{\em F} & \astype{Field} & A field containing R\\
$\iota$ & $R \to F$ & Injection from R into F\\
{\em RX} & \astype{UnivariatePolynomialCategory} R & Polynomials over R\\
{\em RXE} & \astype{LinearOrdinaryRecurrenceCategory} RX & Recurrences over RX\\
{\em FX} & \astype{UnivariatePolynomialCategory} F & Polynomials over F\\
}
\Descr{\this(R, F, $\iota$, RX, RXE, FX) provides a rational solver
for linear ordinary recurrence operators with polynomial coefficients.}
\begin{exports}
\asexp{kernel}: & RXE $\to$ (RX, V UFP) & Rational solutions\\
\asexp{particularSolution}:
& (RXE, Rx) $\to$ (RX, \astype{Partial} UFP) &
A rational solution\\
\asexp{solve}:
& (RXE, Rx) $\to$ (RX, V UFP, \astype{Partial} UFP) &
Rational solutions\\
\end{exports}
\begin{aswhere}
Rx &==& \astype{Fraction} RX\\
UFP &==& \astype{UnivariateFactorialPolynomial}(F, FX)\\
V &==& \astype{Vector}\\
\end{aswhere}
#endif

LinearOrdinaryRecurrenceRationalSolutions(R:Join(GcdDomain, RationalRootRing),
	F:Field, inj: R -> F,
	RX: UnivariatePolynomialCategory R,
	RXE: LinearOrdinaryRecurrenceCategory RX,
	FX: UnivariatePolynomialCategory F): with {
		Denom1: (RXE, Rx) -> RX;
		Denom2: (RXE, Rx) -> RX;

		kernel: RXE -> (RX, V FFX);
#if ALDOC
\aspage{kernel}
\Usage{\name~L}
\Signature{RXE}
{(RX, \astype{Vector} \astype{UnivariateFactorialPolynomial}(F,FX))}
\Params{
{\em L} & RXE & A linear ordinary recurrence operator\\
}
\Retval{Returns $(d, [p_1,\dots,p_m])$ such that $\{p_1/d,\dots,p_m/d\}$ is
a basis for all the rational solutions of $Ly = 0$.}
#endif
		particularSolution: (RXE, Rx) -> (RX, PFX);
#if ALDOC
\aspage{particularSolution}
\Usage{\name(L, g)}
\Signature{(RXE, \astype{Fraction} RX)}{(RX, \astype{Partial} UFP)}
\begin{aswhere}
UFP &==& UnivariateFactorialPolynomial(F, FX)\\
\end{aswhere}
\Params{
{\em L} & RXE & A linear ordinary recurrence operator\\
$g$ & \astype{Fraction} RX & A fraction\\
}
\Retval{Returns ($d$, \failed) if $L y = g$ has no rational
solution, in which case $d$ is a universal denominator for such solutions.
Otherwise, it returns $(d,p)$ such that $p/d$ is a particular solution.}
\seealso{\asexp{solve}}
#endif
		solve: (RXE, Rx) -> (RX, V FFX, PFX);
#if ALDOC
\aspage{solve}
\Usage{\name(L, g)}
\Signature{(RXE, \astype{Fraction} RX)}
{(RX, \astype{Vector} UFP, \astype{Partial} UFP)}
\begin{aswhere}
UFP &==& UnivariateFactorialPolynomial(F, FX)\\
\end{aswhere}
\Params{
{\em L} & RXE & A linear ordinary recurrence operator\\
$g$ & \astype{Fraction} RX & A fraction\\
}
\Retval{Returns $(d, [p_1,\dots,p_s], \alpha)$ where $p_1/d,\dots,p_s/d$ is
a basis for all the rational solutions of $Ly = 0$,
and $\alpha$ is the result that \asexp{particularSolution} would return
on the same input.}
\seealso{\asexp{kernel},\asexp{particularSolution}}
#endif
} == add {
	-- (p,e) means p \sigma^{-1}(p) ... \sigma^{-e}(p)
	-- Then,  \sigma((p,e))/(p,e) = \sigma(p)/\sigma^{-e}(p) by telescoping
	local logder(p:RX, e:Z):Rx == {
		import from R;
		translate(p, -1) / translate(p, e::R);
	}

	local logder(p:PRX):Rx == {
		u:Rx := 1;
		for term in p repeat u := times!(u, logder term);
		u;
	}

	local Rx2FFX(g:Rx):FFX == {
		import from Z, F, RX;
		assert(zero? degree denominator g);
		inv(inj leadingCoefficient denominator g) * RX2FFX numerator g;
	}

	local RX2FFX(p:RX):FFX == {
		import from UnivariateFreeFiniteAlgebra2(R, RX, F, FX);
		map(inj)(p)::FFX;
	}

	solve(L:RXE, g:Rx):(RX, V FFX, PFX) == {
		import from Z, F, FFX, PRX, Automorphism RX,
		  LinearOrdinaryOperatorPolynomialSolutions(R,F,inj,RX,RXE,FFX);
		TRACE("recrat::solve: L = ", L);
		TRACE("recrat::solve: g = ", g);
		zero? g => {
			(den, num) := kernel(L)$%;
			(den, num, [0]);
		}
		(den, L) := primitive(L, inv(shift$RXE));
		TRACE("recrat::solve: den = ", den);
		TRACE("recrat::solve: pp(L,sigma^-1) = ", L);
		empty?(d := denom(L, g)) => {
			zero? degree denominator g => {
				(hom, part) := solve(L, Rx2FFX g);
				(den, hom, part);
			}
			(den, kernel L, failed);
		}
		TRACE("recrat::solve: d = ", factexpand d);
		(alpha, LL) := twist(L, d);
		TRACE("recrat::solve: alpha = ", alpha);
		TRACE("recrat::solve: LL = ", LL);
		dd := factexpand d;
		g := alpha * dd * g;
		zero? degree denominator g => {
			(hom, part) := solve(LL, Rx2FFX g);
			(den * dd, hom, part);
		}
		(den * dd, kernel LL, failed);
	}

	particularSolution(L:RXE, g:Rx):(RX, PFX) == {
		import from Z, F, FFX, PRX, Automorphism RX,
		  LinearOrdinaryOperatorPolynomialSolutions(R,F,inj,RX,RXE,FFX);
		TRACE("recrat::particularSolution: L = ", L);
		TRACE("recrat::particularSolution: g = ", g);
		zero? g => (1, [0]);
		(den, L) := primitive(L, inv(shift$RXE));
		TRACE("recrat::particularSolution: den = ", den);
		TRACE("recrat::particularSolution: pp(L,sigma^-1) = ", L);
		empty?(d := denom(L, g)) => {
			zero? degree denominator g =>
				(den, particularSolution(L, Rx2FFX g));
			(den, failed);
		}
		TRACE("particularSolution: d = ", factexpand d);
		(alpha, LL) := twist(L, d);
		TRACE("recrat::particularSolution: alpha = ", alpha);
		TRACE("recrat::particularSolution: LL = ", LL);
		dd := factexpand d;
		g := alpha * dd * g;
		zero? degree denominator g =>
			(den * dd, particularSolution(LL, Rx2FFX g));
		(den * dd, failed);
	}

	kernel(L:RXE):(RX, V FFX) == {
		import from PRX, Rx, Automorphism RX,
		  LinearOrdinaryOperatorPolynomialSolutions(R,F,inj,RX,RXE,FFX);
		TRACE("recrat::kernel: L = ", L);
		L := primitivePart L;
		TRACE("recrat::kernel: pp(L) = ", L);
		(den, L) := primitive(L, inv(shift$RXE));
		TRACE("recrat::kernel: den = ", den);
		TRACE("recrat::kernel: pp(L,sigma^-1) = ", L);
		empty?(d := denom(L, 0)) => (den, kernel L);
		TRACE("recrat::kernel: d = ", factexpand d);
		(alpha, LL) := twist(L, d);
		TRACE("recrat::kernel: alpha = ", alpha);
		TRACE("recrat::kernel: LL = ", LL);
		(den * factexpand d, kernel LL);
	}

	-- returns (alpha, LL) s.t. LL = alpha L(d/sigma(d) E)
	local twist(L:RXE, d:PRX):(RX, RXE) == {
		import from Z, Rx, RxE,
			UnivariateFreeFiniteAlgebraOverFraction(RX,RXE,Rx,RxE);
		makeIntegral compose(makeRational L, monomial(inv logder d, 1));
	}

	local fact(p:RX, n:Z):RX == {
		import from R;
		TRACE("recrat::fact: p = ", p);
		TRACE("recrat::fact: n = ", n);
		assert(n >= 0);
		prod := copy p;
		TRACE("recrat::fact: prod = ", prod);
		for i in 1..n repeat {
			p := translate(p, 1);	-- p(x-1);
			TRACE("recrat::fact: p = ", p);
			prod := times!(prod, p);
			TRACE("recrat::fact: prod = ", prod);
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

	local denom(L:RXE, g:Rx):PRX == denom2(L, denominator g);

	Denom1(L:RXE, g:Rx):RX == {
		import from Automorphism RX;
		if zero? g then L := primitivePart L;
		(den, L) := primitive(L, inv(shift$RXE));
		den * denom1(L, g);
	}

	Denom2(L:RXE, g:Rx):RX == {
		import from Automorphism RX;
		if zero? g then L := primitivePart L;
		(den, L) := primitive(L, inv(shift$RXE));
		den * factexpand denom2(L, denominator g);
	}

	denom1(L:RXE, g:Rx):RX == {
		import from Boolean, Z, R,LinearRecurrenceCategoryTools(RX,RXE);
		assert(~zero? L);
		denrhs := denominator g;
		(a0, n0) := trailingMonomial L;
		b := denrhs * a0;
		(an, n) := leadingMonomial L;
		a := denrhs * an;
		zero?(order := n0 - n) => translate(a, n0::R);
		assert(order < 0);
		zero?(h := max(0, dispersion(a, b) + next order)) => 1;
		Lh := section(shift(L, -n0), h);
		if ~zero? g then {
			import from String;
			error "denom1: can only handle homogeneous eqs for now";
		}
		d:RX := 0;
		for term in Lh repeat {
			(c, n) := term;
			d := gcd(d, translate(c, (n*h)::R));
			zero? degree d => return 1;
		}
		translate(d, n0::R);
	}

	-- return [(g1,e1),...,(gk,ek)] where
	-- (g,e) means g \sigma^{-1}(g) ... \sigma^{-e}(g)
	local denom2(L:RXE, denrhs:RX):PRX == {
		import from Boolean, Z;
		assert(~zero? L); assert(~zero? denrhs);
		(a0, n0) := trailingMonomial L;
		b := denrhs * a0;
		(an, n) := leadingMonomial L;
		a := denrhs * an;
		rn0 := n0::R;
		zero?(order := n0 - n) => cons((translate(a, rn0),0), empty);
		assert(order < 0);
		ans := universalBound(translate(a, (-order)::R), b);
		zero? n0 or empty? ans => ans;
		u:PRX := empty;
		for pair in ans repeat {
			(g, m) := pair;
			u := cons((translate(g, rn0), m), u);
		}
		u;
	}
}
