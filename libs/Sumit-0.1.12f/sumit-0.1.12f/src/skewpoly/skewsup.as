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
----------------------------- skewsup.as --------------------------------
#include "sumit"

#if ASDOC
\thistype{SparseUnivariateSkewPolynomial}
\History{Manuel Bronstein}{4/11/94}{created}
\Usage{
import from \this(R, $\sigma$, $\delta$);\\
import from \this(R, $\sigma$, $\delta$, x);\\
}
\Params{
{\em R} & CommutativeRing & The coefficient ring of the polynomials\\
{\em $\sigma$} & Automorphism R & The automorphism to use\\
{\em $\delta$} & R $\to$ R & The $\sigma$-derivation to use\\
{\em x} & String & The variable name (optional)\\
}
\Descr{\this(R, $\sigma$, $\delta$, x) implements sparse skew univariate
polynomials with coefficients in R.}
\begin{exports}
\category{UnivariateSkewPolynomialCategory R}\\
\end{exports}
#endif

macro {
	Z == Integer;
	Symbol == String;
	anon == "\Box";
}

SparseUnivariateSkewPolynomial(R:CommutativeRing, sigma:Automorphism R,
	delta:R -> R,
		avar:Symbol == anon): UnivariateSkewPolynomialCategory R
== SparseUnivariatePolynomial(R, avar) add {
	macro Rep == SparseUnivariatePolynomial(R, avar);

-- TEMPORARY: % DOES NOT HAVE PROPER CAT (898)
	import from Rep, UnivariateSkewPolynomialCategoryOps(R,_
		% pretend UnivariateSkewPolynomialCategory R);

	(x:%) * (y:%):%				== times(x, y, sigma, delta);
	apply(p:%, c:R, r:R):R			== apply(p, c, r, sigma, delta);

	if R has IntegralDomain then {
		monicLeftDivide(a:%, b:%):(%, %) == monicLeftDivide(a, b,sigma);
		monicRightDivide(a:%, b:%):(%, %)== monicRightDivide(a,b,sigma);

		leftExactQuotient(a:%, b:%):Partial % ==
			leftExactQuotient(a, b, sigma);

		rightExactQuotient(a:%, b:%):Partial % ==
			rightExactQuotient(a, b, sigma);
	}

	if R has Field then {
		leftDivide(a:%, b:%):(%, %)	== leftDivide(a, b, sigma);
		rightDivide(a:%, b:%):(%, %)	== rightDivide(a, b, sigma);
	}
}

#if SUMITTEST
---------------------- test skewsup.as --------------------------
#include "sumittest"

macro {
	Z == Integer;
	Zx == SparseUnivariatePolynomial(Z, "x");
	AU == Automorphism Zx;
	Fd == SparseUnivariateSkewPolynomial(Zx, 1, differentiate, "D");
}

degree():Boolean == {
	import from Z, Zx, AU, Fd;
	x:Zx := monom;
	dx:Fd := monom;
	p := x^2 * dx^2 - x * dx + 1;
	degree p = 2 and leadingCoefficient p = x*x
		and zero?(x + leadingCoefficient reductum p);
}

exactQuotient():Boolean == {
	import from Z, Zx, AU, Fd, Partial Fd;

	x:Zx := monom;
	dx:Fd := monom;
	p := dx * dx - x::Fd;                   -- p = D^2 - x  (Airy)
	p2 := p * p;
	q := dx^4 - 2*x*dx^2 - (2::Zx)*dx + (x^2)::Fd;	-- q = p
	ql := leftExactQuotient(q, p);        	-- must be p
	qr := rightExactQuotient(p2, p);        -- must be p
	~(failed? ql) and ~(failed? qr) and retract(ql) = p and retract(qr) = p;
}

print << "Testing skewsup..." << newline;
sumitTest("degree", degree);
sumitTest("exactQuotient", exactQuotient);
print << newline;
#endif

