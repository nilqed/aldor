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
----------------------------- sktools.as --------------------------------
#include "sumit"

#if ASDOC
\thistype{UnivariateSkewPolynomialCategoryOps}
\History{Manuel Bronstein}{4/11/94}{created}
\Usage{import from \this(R, C)}
\Params{
{\em R} & CommutativeRing & The coefficient ring of the polynomials\\
{\em C} & UnivariateSkewPolynomialCategory R & A skew-polynomial type\\
}
\Descr{\this(R, C) provides the univariate skew polynomial arithmetic
operations which depend on the $\sigma$ and $\delta$ functions determining
the skew polynomial ring.}
\begin{exports}
apply: & (C, R, R, MOR, R $\to$ R) $\to$ R &
Apply a skew-polynomial to a scalar\\
times: & (C, C, MOR, R $\to$ R) $\to$ C &
Product of skew-polynomials\\
\end{exports}
\begin{exports}[if R has IntegralDomain then]
leftExactQuotient: & (C, C, MOR) $\to$ Partial C &
Left exact quotient\\
monicLeftDivide: & (C, C, MOR) $\to$ (C, C) &
Left Euclidean division\\
monicRightDivide: & (C, C, MOR) $\to$ (C, C) &
Right Euclidean division\\
rightExactQuotient: & (C, C, MOR) $\to$ Partial C &
Right exact quotient\\
\end{exports}
\begin{exports}[if R has Field then]
leftDivide: & (C, C, MOR) $\to$ (C, C) & Left Euclidean division\\
rightDivide: & (C, C, MOR) $\to$ (C, C) & Right Euclidean division\\
\end{exports}
\Aswhere{
MOR &==& Automorphism R\\
}
#endif

macro Z	== Integer;

UnivariateSkewPolynomialCategoryOps(R:CommutativeRing,
	C:UnivariateSkewPolynomialCategory R): with {
		apply: (C, R, R, Automorphism R, R -> R) -> R;
#if ASDOC
\begin{aspage}{apply}
\Usage{ \name(p, c, a, $\sigma$, $\delta$)\\ p(c, a, $\sigma$, $\delta$) }
\Signature{(C, R, R, Automorphism R, R $\to$ R)}{R}
\Params{
{\em p} & \% & A skew polynomial\\
{\em c} & R  & An element of the ring\\
{\em a} & R  & The element to apply $p$ to\\
{\em $\sigma$} & Automorphism R & The automorphism to use\\
{\em $\delta$} & R $\to$ R & The $\sigma$-derivation to use\\
}
\Retval{Returns
$$
\sum_{i=0}^n a_i\, (c \sigma + \delta)^i\, (a)
$$
where $p = \sum_{i=0}^n a_i x^i$.}
\end{aspage}
#endif
		if R has Field then
			leftDivide: (C, C, Automorphism R) -> (C, C);
#if ASDOC
\begin{aspage}{leftDivide}
\Usage{\name(a, b, $\sigma$)}
\Signature{(C, C, Automorphism R)}{(C, C)}
\Params{
{\em a } & \% & The polynomial to be divided\\
{\em b } & \% & The polynomial to divide by\\
{\em $\sigma$} & Automorphism R & The automorphism to use\\
}
\Retval{Returns $(q, r)$ such that $a = b q + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{leftExactQuotient(\this),\\ monicLeftDivide(\this),\\
rightDivide(\this)}
\end{aspage}
#endif
		if R has IntegralDomain then {
			leftExactQuotient: (C, C, Automorphism R) -> Partial C;
#if ASDOC
\begin{aspage}{leftExactQuotient}
\Usage{\name(a, b, $\sigma$)}
\Signature{(C, C, Automorphism R)}{(C, C)}
\Params{
{\em a } & \% & The polynomial to be divided\\
{\em b } & \% & The polynomial to divide by\\
{\em $\sigma$} & Automorphism R & The automorphism to use\\
}
\Retval{Returns either $q$ such that $a = b q$ if such a $q$ exists,
\failed~otherwise.}
\seealso{leftDivide(\this),\\ monicLeftDivide(\this),\\
rightExactQuotient(\this)}
\end{aspage}
#endif
			monicLeftDivide: (C, C, Automorphism R) -> (C, C);
#if ASDOC
\begin{aspage}{monicLeftDivide}
\Usage{\name(a, b, $\sigma$)}
\Signature{(C, C, Automorphism R)}{(C, C)}
\Params{
{\em a } & \% & The polynomial to be divided\\
{\em b } & \% & The polynomial to divide by (must be monic)\\
{\em $\sigma$} & Automorphism R & The automorphism to use\\
}
\Retval{Returns $(q, r)$ such that $a = b q + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{leftDivide(\this),\\ leftExactQuotient(\this),\\
monicRightDivide(\this)}
\end{aspage}
#endif
			monicRightDivide: (C, C, Automorphism R) -> (C, C);
#if ASDOC
\begin{aspage}{monicRightDivide}
\Usage{\name(a, b, $\sigma$)}
\Signature{(C, C, Automorphism R)}{(C, C)}
\Params{
{\em a } & \% & The polynomial to be divided\\
{\em b } & \% & The polynomial to divide by (must be monic)\\
{\em $\sigma$} & Automorphism R & The automorphism to use\\
}
\Retval{Returns $(q, r)$ such that $a = q b + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{monicLeftDivide(\this),\\ rightDivide(\this),\\
rightExactQuotient(\this)}
\end{aspage}
#endif
		}
		if R has Field then
			rightDivide: (C, C, Automorphism R) -> (C, C);
#if ASDOC
\begin{aspage}{rightDivide}
\Usage{\name(a, b, $\sigma$)}
\Signature{(C, C, Automorphism R)}{(C, C)}
\Params{
{\em a } & \% & The polynomial to be divided\\
{\em b } & \% & The polynomial to divide by\\
{\em $\sigma$} & Automorphism R & The automorphism to use\\
}
\Retval{Returns $(q, r)$ such that $a = q b + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{leftDivide(\this),\\ monicRightDivide(\this),\\
rightExactQuotient(\this)}
\end{aspage}
#endif
		if R has IntegralDomain then
			rightExactQuotient: (C, C, Automorphism R) -> Partial C;
#if ASDOC
\begin{aspage}{rightExactQuotient}
\Usage{\name(a, b, $\sigma$)}
\Signature{(C, C, Automorphism R)}{(C, C)}
\Params{
{\em a } & \% & The polynomial to be divided\\
{\em b } & \% & The polynomial to divide by\\
{\em $\sigma$} & Automorphism R & The automorphism to use\\
}
\Retval{Returns either $q$ such that $a = q b$ if such a $q$ exists,
\failed~otherwise.}
\seealso{leftExactQuotient(\this),\\ monicRightDivide(\this),\\
rightDivide(\this)}
\end{aspage}
#endif
		times: (C, C, Automorphism R, R -> R) -> C;
#if ASDOC
\begin{aspage}{times}
\Usage{\name(p, q, $\sigma$, $\delta$)}
\Signature{(C, C, Automorphism R, R $\to$ R)}{C}
\Params{
{\em p} & \% & A skew polynomial\\
{\em q} & \% & A skew polynomial\\
{\em $\sigma$} & Automorphism R & The automorphism to use\\
{\em $\delta$} & R $\to$ R & The $\sigma$-derivation to use\\
}
\Retval{Returns the product $p q$ as skew-polynomials.}
\end{aspage}
#endif
} == add {
	times(x:C, y:C, sigma:Automorphism R, delta:R -> R):C == {
		import from R;
		zero? y => 0;
		z:C := 0;
		d:Z := 0;
		-- traverse right to left to get quadratic complexity
		-- (cubic if left to right because termPoly depends on n)
		for term in reverse x repeat {
			(c, n) := term;
			-- TEMPORARY: SHOULD DO THIS IN-PLACE EVENTUALLY
			y := termPoly(1, n - d, y, sigma, delta);
			z := add!(z, c * y);
			d := n;
		}
		z;
	}

	-- computes a x^n y (noncommutative, complexity is n degree(y))
	local termPoly(a:R, n:Z, y:C, sigma:Automorphism R, delta:R -> R):C == {
		ASSERT(n >= 0);
		zero? y => 0;
		for i in 1..n repeat y := xtimes(y, sigma, delta);
		a * y;
	}

	-- computes x^1 y (noncommutative, complexity is degree(y))
	local xtimes(y:C, sigma:Automorphism R, delta:R -> R):C == {
		import from Z;
		z:C := 0;
		for term in y repeat {
			(a, n) := term;
			z := add!(add!(z, sigma a, next n), delta a, n);
		}
		z;
	}

	apply(p:C, c:R, x:R, sigma:Automorphism R, delta:R -> R):R == {
		import from Z;
		w:R  := 0;
		zero? x => w;
		xn:R := x;
		d:Z := 0;
		for term in reverse p repeat {
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
	local localLeftDivide(a:C, b:C, sigma:Automorphism R, b1:R):(C, C) == {
		ASSERT(not zero? b);
		import from Z, R;
		n := degree(a) - (m := degree b);
		zero? a or n < 0 => (0, a);
		q0 := monomial((sigma^(-m))(b1 * leadingCoefficient a), n);
		(q, r) := localLeftDivide(a - b * q0, b, sigma, b1);
		(q + q0, r)
	}

	-- localRightDivide(a, b) returns (q, r) such that a = q b + r
	-- b1 is the inverse of the leadingCoefficient of b
	local localRightDivide(a:C, b:C, sigma:Automorphism R, b1:R):(C, C) == {
		ASSERT(not zero? b);
		import from SingleInteger, Z, R, PrimitiveArray C;
		n := retract(degree(a) - (m := degree b));
		zero? a or n < 0 => (0, a);
		localRightDiv(a, b, m, sigma, b1, xtable(b, n));
	}

	-- returns an array t such that t(i+1) = x^i a
	local xtable(a:C, n:SingleInteger):PrimitiveArray C == {
		x:C := monom;
		xa:PrimitiveArray C := new next n;
		xa.1 := a;
		for i in 1..n repeat xa(next i) := x * xa.i;
		xa;
	}

	-- localRightDiv(a, b) returns (q, r) such that a = q b + r
	-- b1 is the inverse of the leadingCoefficient of b
	-- m = degree b
	-- xb is such that xb(i+1) = x^i b
	local localRightDiv(a:C, b:C, m:Z, sigma:Automorphism R, b1:R,
		xb:PrimitiveArray C):(C, C) == {
			import from SingleInteger;
			ASSERT(not zero? b); ASSERT(m = degree b);
			n := degree(a) - m;
			zero? a or n < 0 => (0, a);
			cq0 := leadingCoefficient(a) * (sigma^n) b1;
			-- xb(n+1) = x^n b
			(q, r) := localRightDiv(a - cq0 * xb(retract next n),
							b, m, sigma, b1, xb);
			(q + monomial(cq0, n), r)
	}

	if R has IntegralDomain then {
		leftExactQuotient(a:C, b:C, sigma:Automorphism R):Partial C == {
			ASSERT(not zero? b);
			zero? a => [0];
			import from Z, R, Partial R, Partial C;
			n := degree(a) - (m := degree b);
			n < 0 => failed;
			lb := leadingCoefficient b;
			c := exactQuotient(leadingCoefficient a, lb);
			failed? c => failed;
			q0 := monomial((sigma^(-m))(retract c), n);
			q := leftExactQuotient(a - b * q0, b, sigma);
			failed? q => failed;
			[q0 + retract q];
		}

		rightExactQuotient(a:C,b:C, sigma:Automorphism R):Partial C == {
			ASSERT(not zero? b);
			zero? a => [0];
			import from SingleInteger, Z, R, Partial R, Partial C;
			n := retract(degree(a) - (m := degree b));
			n < 0 => failed;
			rightExactQuo(a, b, m, sigma, leadingCoefficient b,
								xtable(b, n));
		}

		rightExactQuo(a:C, b:C, m:Z, sigma:Automorphism R, lb:R,
			xb:PrimitiveArray C):Partial C == {
			import from SingleInteger, Z, R, Partial R, Partial C;
			ASSERT(not zero? b);
			zero? a => [0];
			n := degree(a) - m;
			n < 0 => failed;
			c := exactQuotient(leadingCoefficient a, (sigma^n) lb);
			failed? c => failed;
			cc := retract c;
			-- xb(n+1) = x^n b
			q := rightExactQuo(a - cc * xb(retract next n),
							b, m, sigma, lb, xb);
			failed? q => failed;
			[monomial(cc, n) + retract q];
		}

		monicLeftDivide(a:C, b:C, sigma:Automorphism R):(C, C) == {
			import from R, Partial R;
			u := leadingCoefficient b;
			ASSERT(unit? u);
			localLeftDivide(a, b, sigma, retract reciprocal u);
		}

		monicRightDivide(a:C, b:C, sigma:Automorphism R):(C, C) == {
			import from R, Partial R;
			u := leadingCoefficient b;
			ASSERT(unit? u);
			localRightDivide(a, b, sigma, retract reciprocal u);
		}
	}

	if R has Field then {
		leftDivide(a:C, b:C, sigma:Automorphism R):(C, C) == {
			import from R;
			localLeftDivide(a, b, sigma, inv leadingCoefficient b);
		}

		rightDivide(a:C, b:C, sigma:Automorphism R):(C, C) == {
			import from R;
			localRightDivide(a, b, sigma, inv leadingCoefficient b);
		}
	}
}

