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
----------------------------- sit_uskwpol.as --------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{UnivariateSkewPolynomial}
\History{Manuel Bronstein}{4/11/94}{created}
\Usage{ import from \this(R, Rx, $\sigma$, $\delta$) }
\Params{
{\em R} & \astype{Ring} & The coefficient ring\\
{\em Rx} & \astype{UnivariatePolynomialCategory} R & A polynomial type over R\\
{\em $\sigma$} & \astype{Automorphism} R & The automorphism to use\\
{\em $\delta$} & R $\to$ R & The $\sigma$-derivation to use\\
}
\Descr{\this(R, Rx, $\sigma$, $\delta$) implements skew univariate
polynomials with coefficients in R. Rx is used for representing
the skew--polynomials, so you can choose between sparse and dense
representations.}
\begin{exports}
\category{\astype{UnivariateSkewPolynomialCategory} R}\\
\end{exports}
#endif

macro Z == Integer;

UnivariateSkewPolynomial(R:Ring, Rx: UnivariatePolynomialCategory R,
	sigma:Automorphism R, delta:R->R):UnivariateSkewPolynomialCategory R ==
	Rx add {
	Rep == Rx;

	import from UnivariateSkewPolynomialCategoryTools(R, %);

	(x:%) * (y:%):%		== times(x, y, sigma, delta);
	apply(p:%, c:R, r:R):R	== apply(p, c, r, sigma, delta);

	if R has IntegralDomain then {
		monicLeftDivide(a:%, b:%):(%, %) ==
			monicLeftDivide(a, b, sigma, delta);

		monicRightDivide(a:%, b:%):(%, %) ==
			monicRightDivide(a, b, sigma, delta);

		leftExactQuotient(a:%, b:%):Partial % ==
			leftExactQuotient(a, b, sigma, delta);

		rightExactQuotient(a:%, b:%):Partial % ==
			rightExactQuotient(a, b, sigma, delta);
	}

	if R has Field then {
		leftDivide(a:%, b:%):(%, %) ==
			leftDivide(a, b, sigma, delta);

		rightDivide(a:%, b:%):(%, %) ==
			rightDivide(a, b, sigma, delta);
	}
}

#if SUMITTEST
---------------------- test sit_uskwpol.as --------------------------
#include "sumittest"

macro {
	Z == Integer;
	Zx == DenseUnivariatePolynomial Z;
	Zxy == DenseUnivariatePolynomial Zx;
	AU == Automorphism Zx;
	Fd == UnivariateSkewPolynomial(Zx, Zxy, 1, differentiate);
}

local degree():Boolean == {
	import from Z, Zx, AU, Fd;
	x:Zx := monom;
	dx:Fd := monom;
	p := x^2 * dx^2 - x * dx + 1;
	degree p = 2 and leadingCoefficient p = x*x
		and zero?(x + leadingCoefficient reductum p);
}

local exactQuotient():Boolean == {
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

stdout << "Testing sit__uskwpol..." << endnl;
sumitTest("degree", degree);
sumitTest("exactQuotient", exactQuotient);
stdout << endnl;
#endif

