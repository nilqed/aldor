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
----------------------------- sit_sktools.as ------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I == MachineInteger;
	Z == Integer;
	ARR == PrimitiveArray;
	V == Vector;
	M == DenseMatrix;
	MOR == Automorphism R;
}

#if ALDOC
\thistype{UnivariateSkewPolynomialCategoryTools}
\History{Manuel Bronstein}{4/11/94}{created}
\Usage{import from \this(R, C)}
\Params{
{\em R} & \astype{Ring} & The coefficient ring\\
{\em C}
& \astype{UnivariateSkewPolynomialCategory} R & A skew--polynomial type\\
}
\Descr{\this(R, C) provides the univariate skew polynomial arithmetic
operations which depend on the $\sigma$ and $\delta$ functions determining
the skew polynomial ring.}
\begin{exports}
\asexp{apply}: & (C, R, R, MOR, R $\to$ R) $\to$ R &
Apply a skew-polynomial to a scalar\\
\asexp{times}: & (C, C, MOR, R $\to$ R) $\to$ C &
Product of skew-polynomials\\
\end{exports}
\begin{exports}[if R has \astype{IntegralDomain} then]
\asexp{leftExactQuotient}: & (C, C, MOR, R $\to$ R) $\to$ \astype{Partial} C &
Left exact quotient\\
\asexp{monicLeftDivide}: & (C, C, MOR, R $\to$ R) $\to$ (C, C) &
Left Euclidean division\\
\asexp{monicRightDivide}: & (C, C, MOR, R $\to$ R) $\to$ (C, C) &
Right Euclidean division\\
\asexp{rightExactQuotient}:
& (C, C, MOR, R $\to$ R) $\to$ \astype{Partial} C &
Right exact quotient\\
\end{exports}
\begin{exports}[if R has \astype{Field} then]
\asexp{leftDivide}:
& (C, C, MOR, R $\to$ R) $\to$ (C, C) & Left Euclidean division\\
\asexp{rightDivide}:
& (C, C, MOR, R $\to$ R) $\to$ (C, C) & Right Euclidean division\\
\end{exports}
\begin{aswhere}
MOR &==& \astype{Automorphism} R\\
\end{aswhere}
#endif

UnivariateSkewPolynomialCategoryTools(R:Ring,
	C:UnivariateSkewPolynomialCategory R): with {
		apply: (C, R, R, MOR, R -> R) -> R;
#if ALDOC
\aspage{apply}
\Usage{ \name(p, c, a, $\sigma$, $\delta$)\\ p(c, a, $\sigma$, $\delta$) }
\Signature{(C, R, R, \astype{Automorphism} R, R $\to$ R)}{R}
\Params{
{\em p} & C & A skew polynomial\\
{\em c} & R  & An element of the ring\\
{\em a} & R  & The element to apply $p$ to\\
{\em $\sigma$} & \astype{Automorphism} R & The automorphism to use\\
{\em $\delta$} & R $\to$ R & The $\sigma$-derivation to use\\
}
\Retval{Returns
$$
\sum_{i=0}^n a_i\, (c \sigma + \delta)^i\, (a)
$$
where $p = \sum_{i=0}^n a_i x^i$.}
#endif
		if R has Field then {
			leftDivide: (C, C, MOR, R -> R) -> (C, C);
#if ALDOC
\aspage{leftDivide}
\Usage{\name(a, b, $\sigma$, $\delta$)}
\Signature{(C, C, \astype{Automorphism} R, R $\to$ R)}{(C, C)}
\Params{
{\em a } & C & The skew--polynomial to be divided\\
{\em b } & C & The skew--polynomial to divide by\\
{\em $\sigma$} & \astype{Automorphism} R & The automorphism to use\\
{\em $\delta$} & R $\to$ R & The $\sigma$-derivation to use\\
}
\Retval{Returns $(q, r)$ such that $a = b q + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{\asexp{leftExactQuotient},\asexp{monicLeftDivide},\asexp{rightDivide}}
#endif
		}
		if R has IntegralDomain then {
			leftExactQuotient: (C, C, MOR, R -> R) -> Partial C;
#if ALDOC
\aspage{leftExactQuotient}
\Usage{\name(a, b, $\sigma$, $\delta$)}
\Signature{(C, C, \astype{Automorphism} R, R $\to$ R)}{(C, C)}
\Params{
{\em a } & C & The skew--polynomial to be divided\\
{\em b } & C & The skew--polynomial to divide by\\
{\em $\sigma$} & \astype{Automorphism} R & The automorphism to use\\
{\em $\delta$} & R $\to$ R & The $\sigma$-derivation to use\\
}
\Retval{Returns either $q$ such that $a = b q$ if such a $q$ exists,
\failed~otherwise.}
\seealso{\asexp{leftDivide},\asexp{monicLeftDivide},\asexp{rightExactQuotient}}
#endif
			monicLeftDivide: (C, C, MOR, R -> R) -> (C, C);
#if ALDOC
\aspage{monicLeftDivide}
\Usage{\name(a, b, $\sigma$, $\delta$)}
\Signature{(C, C, \astype{Automorphism} R, R $\to$ R)}{(C, C)}
\Params{
{\em a } & C & The skew--polynomial to be divided\\
{\em b } & C & The skew--polynomial to divide by (must be monic)\\
{\em $\sigma$} & \astype{Automorphism} R & The automorphism to use\\
{\em $\delta$} & R $\to$ R & The $\sigma$-derivation to use\\
}
\Retval{Returns $(q, r)$ such that $a = b q + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{\asexp{leftDivide},\asexp{leftExactQuotient},\asexp{monicRightDivide}}
#endif
			monicRightDivide: (C, C, MOR, R -> R) -> (C, C);
#if ALDOC
\aspage{monicRightDivide}
\Usage{\name(a, b, $\sigma$, $\delta$)}
\Signature{(C, C, \astype{Automorphism} R, R $\to$ R)}{(C, C)}
\Params{
{\em a } & C & The skew--polynomial to be divided\\
{\em b } & C & The skew--polynomial to divide by (must be monic)\\
{\em $\sigma$} & \astype{Automorphism} R & The automorphism to use\\
}
\Retval{Returns $(q, r)$ such that $a = q b + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{\asexp{monicLeftDivide},\asexp{rightDivide},\asexp{rightExactQuotient}}
#endif
		}
		if R has Field then {
			rightDivide: (C, C, MOR, R -> R) -> (C, C);
#if ALDOC
\aspage{rightDivide}
\Usage{\name(a, b, $\sigma$, $\delta$)}
\Signature{(C, C, \astype{Automorphism} R, R $\to$ R)}{(C, C)}
\Params{
{\em a } & C & The skew--polynomial to be divided\\
{\em b } & C & The skew--polynomial to divide by\\
{\em $\sigma$} & \astype{Automorphism} R & The automorphism to use\\
}
\Retval{Returns $(q, r)$ such that $a = q b + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{\asexp{leftDivide},\asexp{monicRightDivide},\asexp{rightExactQuotient}}
#endif
		}
		if R has IntegralDomain then {
			rightExactQuotient: (C, C, MOR, R -> R) -> Partial C;
#if ALDOC
\aspage{rightExactQuotient}
\Usage{\name(a, b, $\sigma$, $\delta$)}
\Signature{(C, C, \astype{Automorphism} R, R $\to$ R)}{(C, C)}
\Params{
{\em a } & C & The skew--polynomial to be divided\\
{\em b } & C & The skew--polynomial to divide by\\
{\em $\sigma$} & \astype{Automorphism} R & The automorphism to use\\
}
\Retval{Returns either $q$ such that $a = q b$ if such a $q$ exists,
\failed~otherwise.}
\seealso{\asexp{leftExactQuotient},\asexp{monicRightDivide},\asexp{rightDivide}}
#endif
		}
		times: (C, C, MOR, R -> R) -> C;
#if ALDOC
\aspage{times}
\Usage{\name(p, q, $\sigma$, $\delta$)}
\Signature{(C, C, \astype{Automorphism} R, R $\to$ R)}{C}
\Params{
{\em p} & C & A skew polynomial\\
{\em q} & C & A skew polynomial\\
{\em $\sigma$} & \astype{Automorphism} R & The automorphism to use\\
{\em $\delta$} & R $\to$ R & The $\sigma$-derivation to use\\
}
\Retval{Returns the product $p q$ as skew-polynomials.}
#endif
} == add {
	times(x:C, y:C, sigma:MOR, delta:R -> R):C == {
		import from R;
		zero? y => 0;
		z:C := 0;
		d:Z := 0;
		-- traverse right to left to get quadratic complexity
		-- (cubic if left to right because xntimes depends on n)
		for term in terms x repeat {	-- low to high exponents
			(c, n) := term;
			-- TEMPORARY: SHOULD DO THIS IN-PLACE EVENTUALLY
			y := xntimes(n - d, y, sigma, delta);
			z := add!(z, c * y);
			d := n;
		}
		z;
	}

	-- computes x^n y (noncommutative, complexity is n degree(y))
	local xntimes(n:Z, y:C, sigma:MOR, delta:R -> R):C == {
		assert(n >= 0);
		zero? y => 0;
		for i in 1..n repeat y := xtimes(y, sigma, delta);
		y;
	}

	-- computes x^1 y (noncommutative, complexity is degree(y))
	local xtimes(y:C, sigma:MOR, delta:R -> R):C == {
		import from Z;
		z:C := 0;
		for term in y repeat {
			(a, n) := term;
			z := add!(add!(z, sigma a, next n), delta a, n);
		}
		z;
	}

	apply(p:C, c:R, x:R, sigma:MOR, delta:R -> R):R == {
		import from Z;
		w:R  := 0;
		zero? x => w;
		xn:R := x;
		d:Z := 0;
		for term in terms p repeat {	-- low to high exponents
			(cf, n) := term;
			for i in 1..n - d repeat
				zero?(xn := c * sigma xn + delta xn)=> return w;
			w := add!(w, cf * xn);
			d := n;
		}
		w;
	}

	-- localLeftDivide(a, b) returns (q, r) such that a = b q + r
	-- b1 is the inverse of the leadingCoefficient of b
	local localLeftDivide(a:C, b:C, sigma:MOR, delta:R -> R, b1:R):(C,C)=={
		assert(not zero? b);
		import from Z, R;
		n := degree(a) - (m := degree b);
		zero? a or n < 0 => (0, a);
		q0 := monomial((sigma^(-m))(b1 * leadingCoefficient a), n);
		(q, r) := localLeftDivide(a - times(b, q0, sigma, delta),
							b, sigma, delta, b1);
		(q + q0, r)
	}

	-- localRightDivide(a, b) returns (q, r) such that a = q b + r
	-- b1 is the inverse of the leadingCoefficient of b
	local localRightDivide(a:C, b:C, sigma:MOR, delta:R->R, b1:R):(C,C) == {
		assert(not zero? b);
		import from I, Z, R, ARR C;
		n := machine(degree(a) - (m := degree b));
		zero? a or n < 0 => (0, a);
		localRightDiv(a, b, m, sigma, b1, xtable(b, n, sigma, delta));
	}

	-- returns an array t such that t.i = x^i a
	local xtable(a:C, n:I, sigma:MOR, delta:R -> R):ARR C == {
		x:C := monom;
		xa:ARR C := new next n;
		xa.0 := a;
		for i in 0..prev n repeat
			xa(next i) := xtimes(xa.i, sigma, delta);
		xa;
	}

	-- localRightDiv(a, b) returns (q, r) such that a = q b + r
	-- b1 is the inverse of the leadingCoefficient of b
	-- m = degree b
	-- xb is such that xb.i = x^i b
	local localRightDiv(a:C, b:C, m:Z, s:MOR, b1:R, xb:ARR C):(C, C) == {
		import from I;
		assert(not zero? b); assert(m = degree b);
		n := degree(a) - m;
		zero? a or n < 0 => (0, a);
		cq0 := leadingCoefficient(a) * (s^n) b1;
		-- xb.n = x^n b
		(q, r) := localRightDiv(a - cq0*xb(machine n), b, m, s, b1, xb);
		(q + monomial(cq0, n), r)
	}

	if R has IntegralDomain then {
		leftExactQuotient(a:C, b:C, sigma:MOR, delta:R->R):Partial C=={
			assert(not zero? b);
			zero? a => [0];
			import from Z, R, Partial R;
			n := degree(a) - (m := degree b);
			n < 0 => failed;
			lb := leadingCoefficient b;
			c := exactQuotient(leadingCoefficient a, lb);
			failed? c => failed;
			q0 := monomial((sigma^(-m))(retract c), n);
			q := leftExactQuotient(a - times(b, q0, sigma, delta),
								b, sigma,delta);
			failed? q => failed;
			[q0 + retract q];
		}

		rightExactQuotient(a:C, b:C, sigma:MOR, delta:R->R):Partial C=={
			assert(not zero? b);
			zero? a => [0];
			import from I, Z, R, Partial R;
			n := machine(degree(a) - (m := degree b));
			n < 0 => failed;
			rightExactQuo(a, b, m, sigma, leadingCoefficient b,
						xtable(b, n, sigma, delta));
		}

		rightExactQuo(a:C,b:C,m:Z,sigma:MOR,lb:R,xb:ARR C):Partial C=={
			import from I, Z, R, Partial R;
			assert(not zero? b);
			zero? a => [0];
			n := degree(a) - m;
			n < 0 => failed;
			c := exactQuotient(leadingCoefficient a, (sigma^n) lb);
			failed? c => failed;
			cc := retract c;
			-- xb.n = x^n b
			q := rightExactQuo(a - cc * xb(machine n),
							b, m, sigma, lb, xb);
			failed? q => failed;
			[monomial(cc, n) + retract q];
		}

		monicLeftDivide(a:C, b:C, sigma:MOR, delta:R -> R):(C, C) == {
			import from R, Partial R;
			u := leadingCoefficient b;
			assert(unit? u);
			localLeftDivide(a, b, sigma,delta,retract reciprocal u);
		}

		monicRightDivide(a:C, b:C, sigma:MOR, delta:R -> R):(C, C) == {
			import from R, Partial R;
			u := leadingCoefficient b;
			assert(unit? u);
			localRightDivide(a, b,sigma,delta,retract reciprocal u);
		}
	}

	if R has Field then {
		leftDivide(a:C, b:C, sigma:MOR, delta:R -> R):(C, C) == {
			import from R;
			localLeftDivide(a, b, sigma, delta,
						inv leadingCoefficient b);
		}

		rightDivide(a:C, b:C, sigma:MOR, delta:R -> R):(C, C) == {
			import from R;
			localRightDivide(a, b, sigma, delta,
						inv leadingCoefficient b);
		}
	}
}

