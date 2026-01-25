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
------------------------- horder2.as --------------------------
#include "sumit"

#if ASDOC
\thistype{HeuristicSecondOrderLODOFactorizer}
\History{Manuel Bronstein}{8/1/98}{created}
\Usage{import from \this(R, Rx, Rxd)}
\Params{
{\em R} & IntegerCategory & An integer-like ring\\
{\em Rx} & UnivariatePolynomialCategory R & Coefficients of the equations\\
{\rm Rxd} & LinearOrdinaryDifferentialOperatorCategory Rx &
The differential equations\\
}
\Descr{\this(R, Rx, Rxd) implements a modular heuristic for factoring
second order linear ordinary differential equations in $R(x)[\frac d{dx}]$.}
\begin{exports}
rightFactor: &
Rxd $\to$ Union(factor:Quotient Rx, irreducible:Integer, failed:List Integer)&\\
& Irreducible right factor & \\
\end{exports}
#endif

macro {
	I	== SingleInteger;
	Z	== Integer;
	Rx	== Quotient RX;
	RF	== Cross(RX, RX);
	U	== Union(factor:Rx, irreducible:Z, failed:List RX);
}

HeuristicSecondOrderLODOFactorizer(R:IntegerCategory,
			RX:UnivariatePolynomialCategory R,
			Rxd:LinearOrdinaryDifferentialOperatorCategory RX):with{
		rightFactor: Rxd -> U;
#if ASDOC
\aspage{rightFactor}
\Usage{\name~L}
\Signature{Rxd}
{Union(factor:Quotient Rx, irreducible:Integer, failed:List RX)}
\Params{ {\em L} & Rxd & A second order differential operator\\ }
\Retval{
\name(L) returns $[{\tt irreducible}:\ast]$
if $L$ is irreducible in $R(x)[d/dx]$,
$[factor:u]$ if $L$ is divisible on the right by $d/dx - u$,
and $[failed:[q_1, q_2,\dots, q_n]]$ of increasing degrees,
if the modular heuristic has failed,
in which case the denominators of the $u$'s such
that $d/dx - u$ divides $L$ on the right are probably in $\{q_1,\dots,q_n\}$.}
#endif
} == add {
	local second(a:RX, b:RX):RX == b;

	local smaller?(p:RX, q:RX):Boolean == {
		import from Z;
		degree p < degree q;
	}

	local getPrime(p:I, a:R):I == {
		import from I, SmallPrimes, Partial R;
		p := nextPrime p;
		while (~zero? p) and ~failed?(exactQuotient(a, p::R)) repeat
			p := nextPrime p;
		p > 200 => 0;
		p;
	}

	rightFactor(L:Rxd):U == {
		import from I, Z, R, RX, List RX, ListSort RX, List RF;
		ASSERT(degree L = 2);
		START__TIME;
		secondPrime?:Boolean := false;
		lc := content leadingCoefficient L;
		p1 := p := getPrime(20, lc);
		l1:List RF := empty();
		zerocurv:I := 0;
		while p ~= 0 repeat {
			TRACE("horder2::rightFactor, trying prime ", p::R);
			(code, l) := tryprime(L, lc, ZechPrimeField p);
			TIME("horder2::rightFactor: modular factorization at ");
			code = 2 => return [0@Z];	-- irreducibility
			if code = 1 then {		-- factor(s) found mod p
				secondPrime? => return merge(L, p1, l1, p, l);
				p1 := p; l1 := l; secondPrime? := true;
			}
			else zerocurv := next zerocurv;	-- zero curvature
			p := { zerocurv < 3 => getPrime(p, lc); 0 }
		}
		TIME("horder2::rightFactor: failure at ");
		[sort(smaller?, [second u for u in l1])]; -- failure (0/1 prime)
	}

	-- given than L is divisible by D - u mod p1 for u in l1
	--                       and by D - v mod p2 for v in l2
	-- attempts to find a factor of L in characteristic 0
	local merge(L:Rxd, p1:I, l1:List RF, p2:I, l2:List RF):U == {
		import from List RX;
		lden:List RX := empty();
		for u1 in l1 repeat {
			(a1, b1) := u1;
			for u2 in l2 repeat {
				(a2, b2) := u2;
				u := merge(L, p1, a1, b1, p2, a2, b2);
				u case factor => return u;
				ASSERT(u case failed);
				if ~empty?(u.failed) then {
					ASSERT(empty? rest(u.failed));
					lden := cons(first(u.failed), lden);
				}
			}
		}
		[lden];
	}

	-- given than L is divisible by D-a1/b1 mod p1 and by D-a2/b2 mod p2
	-- attempts to find a factor of L in characteristic 0
	local merge(L:Rxd,p1:I,a1:RX, b1:RX, p2:I, a2:RX, b2:RX):U == {
		import from Z, R, ChineseRemaindering R, Rx, List RX;
		TRACE("horder2::merge, p1 = ", p1); TRACE("p2 = ", p2);
		TRACE("a1 = ", a1); TRACE("a2 = ", a2);
		TRACE("b1 = ", b1); TRACE("b2 = ", b2);
		ASSERT(~zero? b1); ASSERT(~zero? b2);
		-- since this heuristic only finds factors of the form a/b
		-- where a is in Q[x] and b is monic in Z[x], we only need
		-- to consider the pair (b1, b2) if they have the same degree
		degree b1 ~= degree b2 => [empty()$List(RX)];
		comb := combine(p1::R, p2::R);
		d := combine(comb, b1, b2);	-- candidate denominator
		u := combine(comb, a1, a2) / d;
		TRACE("u = ", u);
		a := leadingCoefficient L;
		b := coefficient(L, 1);
		c := coefficient(L, 0);
		-- a D^2 + b D + c is divisible on the right by D - u
		-- if and only if a (u' + u^2) + b u + c = 0
		zero?(a * (u^2 + deriv u) + b * u + c::Rx) => [u];
		TRACE("horder2::merge, failed with denominator ", d);
		[[d]$List(RX)];
	}

	local deriv(u:Rx):Rx == {
		import from Derivation RX, Derivation Rx;
		d := derivation$Rxd;
		dd := lift d;
		dd u;
	}

	local combine(f:(R, R) -> R, u1:RX, u2:RX):RX == {
		import from Z;
		zero? u1 and zero? u2 => 0;
		d := {
			zero? u1 => degree u2;
			zero? u2 => degree u1;
			max(degree u1, degree u2);
		}
		p:RX := 0;
		for n in d..0 by -1 repeat
			p := add!(p, f(coefficient(u1,n),coefficient(u2,n)), n);
		p;
	}

	macro {
		FX  == DenseUnivariatePolynomial F;
		Fx  == Quotient FX;
		Fxd == LinearOrdinaryDifferentialOperator Fx;
	}

	-- lc = content(lcoeff(L)), use it to force it as content
	-- on the denominators of the merged functions
	local tryprime(L:Rxd, lc:R, F:PrimeFieldCategory):(R, List RF) == {
		import from I, Z, Fx, List Fxd, List List Fxd;
		import from ModularLODOReduction(R, RX, Rxd, F, FX, Fxd);
		import from ModularSecondOrderLODOFactorizer(F, FX, Fxd);
		empty?(l := factor reduce L) => (0, empty());
		empty? rest l and empty? rest first l => (2, empty());
		lcp := integer(lc)::F;
		p:I := retract(characteristic$F);
		p2 := shift(p, -1);
		(1, [lift(F, lcp, p, p2, - coefficient(last q, 0)) for q in l]);
	}

	-- balanced lifting, also changes the sign
	local lift(F:PrimeFieldCategory, lc:F, p:I, p2:I, c:Fx):RF == {
		import from FX;
		(lift(F, p, p2, lc * numerator c),
					lift(F, p, p2, lc * denominator c));
	}

	-- balanced lifting
	local lift(F:PrimeFieldCategory, p:I, pover2:I, pp:FX):RX == {
		import from Z, F, R;
		p:RX := 0;
		for term in pp repeat {
			(c, n) := term;
			cc := lift c;
			if cc > pover2 then cc := cc - p;
			p := add!(p, cc::R, n);
		}
		p;
	}
}
