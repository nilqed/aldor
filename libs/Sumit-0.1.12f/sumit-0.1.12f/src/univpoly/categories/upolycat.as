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
----------------------------- upolycat.as ----------------------------------
#include "sumit"

#if ASDOC
\thistype{UnivariatePolynomialCategory}
\History{Manuel Bronstein}{20/5/94}{created}
\History{Manuel Bronstein}{20/9/95}{added check for UnivariateGcdRing}
\Usage{\this~R: Category}
\Params{ {\em R} & SumitRing & The coefficient ring of the polynomials\\ }
\Descr{\this~is the category of univariate polynomials with coefficients in
an arbitrary ring R.}
\begin{exports}
\category{UnivariatePolynomialCategory0~R}\\
\end{exports}
\begin{exports}[if $R$ has FactorizationRing then]
factor: & \% $\to$ (R, Product \%) & Factorisation into irreducibles\\
\end{exports}
\begin{exports}[if $R$ has RationalRootRing then]
\category{RationalRootRing}\\
integerRoots: & \% $\to$ List RationalRoot & Integer roots\\
rationalRoots: & \% $\to$ List RationalRoot & Rational roots\\
\end{exports}
#endif

macro {
	Z == Integer;
	UPC0 == UnivariatePolynomialCategory0 %;
	RR == RationalRoot;
	RES == Resultant(R pretend IntegralDomain, %);
}

UnivariatePolynomialCategory(R:SumitRing):Category ==
	UnivariatePolynomialCategory0 R with {
	if R has FactorizationRing then {
		factor: % -> (R, Product %);
#if ASDOC
\aspage{factor}
\Usage{ \name~p }
\Signature{\%}{(R, Product \%)}
\Params{ {\em p} & P & A polynomial\\ }
\Retval{Returns $(c, p_1^{e_1} \cdots p_n^{e_n})$ such that
each $p_i$ is irreducible, the $p_i$'s have no common factors, and
$$
p = c\;\prod_{i=1}^n p_i^{e_i}\,.
$$
}
#endif
	}
	if R has RationalRootRing then {
		RationalRootRing;
		integerRoots: % -> List RR;
#if ASDOC
\aspage{integerRoots}
\Usage{ \name~p }
\Signature{\%}{List RationalRoot}
\Params{ {\em p} & P & A polynomial\\ }
\Retval{Return $[(r_1,e_1),\dots,(r_n,e_n)]$ where the $r_i$'s are
the integer roots of $p$ and have multiplicity $e_i$.}
#endif
		rationalRoots: % -> List RR;
#if ASDOC
\aspage{rationalRoots}
\Usage{ \name~p }
\Signature{\%}{List RationalRoot}
\Params{ {\em p} & P & A polynomial\\ }
\Retval{Return $[(r_1,e_1),\dots,(r_n,e_n)]$ where the $r_i$'s are
the rational roots of $p$ and have multiplicity $e_i$.}
#endif
	}
	default {
		local gcd?:Boolean == R has GcdDomain;

		if R has IntegralDomain then {
			resultant(p:%, q:%):R == resultant(p, q)$RES;
		}

		if R has GcdDomain then {
			local gcdproject(P:UPC0, p:P):% == {
				import from Z;
				ASSERT(~zero? p);
				q:% := 0;
				for i in 0..degree p repeat
					q := gcd(q, project(P, p, i));
				q;
			}

-- TEMPORARY: WHEN algebraic extensions have good gcd algorithms
#if MULTIGCD
			gcd(l:List %):% == {
				import from MultiGcd(R pretend GcdDomain, %);
				(g, lq) := multiGcd l;
				g;
			}

			gcdquo(l:List %):(%, List %) == {
				import from MultiGcd(R pretend GcdDomain, %);
				multiGcd l;
			}
#endif

			local ugring?:Boolean	== R has UnivariateGcdRing;
			local field?:Boolean	== R has SumitField;
			local infCharp?:Boolean == R has FiniteCharacteristic
							and ~(R has Finite);

			gcd(p:%, q:%):%	== {
				ugring? => ugGcd(p, q);
				field? => eucl(p, q);
				subResultantGcd(p, q)$RES;
			};

			-- destroys p and q
			gcd!(p:%, q:%):% == {
				ugring? => ugGcd!(p, q);
				field? => eucl!(p, q);
				subResultantGcd(p, q)$RES;
			}

			squareFree(p:%):(R, Product %) == {
				import from Integer,
					UnivariatePolynomialSquareFree(R
						 pretend GcdDomain, %);
				infCharp? => musser p;
				yun p;
			}

			if R has UnivariateGcdRing then {
				local ugGcd(p:%, q:%):% == {
					import from R;
					gcdUP(%)(p, q);
				}

				local ugGcd!(p:%, q:%):% == {
					import from R;
					gcdUP!(%)(p, q);
				}

				gcdquo(p:%, q:%):(%, %, %) == {
					import from R;
					gcdquoUP(%)(p, q);
				}
			}

			if R has SumitField then {
				local eucl(p:%, q:%):%	== monic euclid(p, q);
				local eucl!(p:%, q:%):%	== monic! euclid!(p, q);
			}
		}

		if R has FactorizationRing then {
			factor(p:%):(R, Product %) == {
				import from R;
				factor(%)(p);
			}
		}

		if R has RationalRootRing then {
			integerRoots(p:%):List RR  == (integerRoots(%)$R)(p);
			rationalRoots(p:%):List RR == (rationalRoots(%)$R)(p);

			local roots(P:UPC0, p:P, f:% -> List RR):List RR ==
				f project(P, p);

			integerRoots(P:UPC0):P -> List RR ==
				(p:P):List(RR) +-> roots(P, p, integerRoots$%);

			rationalRoots(P:UPC0):P -> List RR ==
				(p:P):List(RR) +-> roots(P, p, rationalRoots$%);


			local project(P:UPC0, p:P):% == {
				import from Z;
				zero? p => 0;
				gcd? => gcdproject(P, p);
				q:% := 1;
				for i in 0..degree p repeat
					q := times!(q, project(P, p, i));
				q;
			}

			local project(P:UPC0, p:P, m:Z):% == {
				q:% := 0;
				for term in p repeat {
					(c, n) := term;
					q := add!(q, coefficient(c, m), n);
				}
				q;
			}
		}
	}
}
