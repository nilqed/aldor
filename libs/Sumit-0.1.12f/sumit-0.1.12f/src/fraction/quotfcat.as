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
------------------------ quotfcat.as ---------------------------
#include "sumit"

macro {
	I == SingleInteger;
	ARR == PrimitiveArray;
}

#if ASDOC
\thistype{QuotientFieldCategory}
\History{Laurent Bernardin}{1/12/94}{created}
\Usage{\this~R: Category}
\Params{ {\em R} & IntegralDomain & an integral domain\\ }
\Descr{\this~R is the category of the quotient fields of R.}
\begin{exports}
\category{QuotientFieldCategory0 R}\\
\end{exports}
#endif
QuotientFieldCategory(R: IntegralDomain): Category ==
	QuotientFieldCategory0 R with {
	default {
	macro {
		MR == DenseMatrix R;
		PR == DenseUnivariatePolynomial R;
		P0 == % pretend QuotientFieldCategory0 R;
	}

	if R has LinearAlgebraRing then {
		determinant(M:MatrixCategory0 %):M -> % == {
			import from I, R, MR, Vector R,
				MatrixCategoryOverQuotient(R, MR, P0, M);
			detR := determinant MR;
			(m:M):% +-> {
				n := rows m;
				assert(n = cols m);
				mr:MR := zero(n, n);
				denom:R := 1;
				for i:I in 1..n repeat {
					(a, v) := makeRowIntegral(m, i);
					denom := denom * a;
					for j in 1..n repeat mr(i,j) := v.j;
				}
				detR(mr) / denom;
			}
		}

		rank(M:MatrixCategory0 %):M -> I == {
			import from R, MR,
				MatrixCategoryOverQuotient(R, MR, P0, M);
			rankR := rank MR;
			(m:M):I +-> rankR makeRowIntegral m;
		}

		span(M:MatrixCategory0 %):M -> (I, ARR I) == {
			import from R, MR,
				MatrixCategoryOverQuotient(R, MR, P0, M);
			spanR := span MR;
			(m:M):(I, ARR I) +-> spanR makeRowIntegral m;
		}

		nullSpace(M:MatrixCategory0 %):M -> List Vector % == {
			import from R, MR, List Vector R,
				VectorOverQuotient(R, P0),
				MatrixCategoryOverQuotient(R, MR, P0, M);
			nullR := nullSpace MR;
			(m:M):List Vector % +-> {
				lr := nullR makeRowIntegral m;
				lq:List Vector % := empty();
				for v in lr repeat
					lq := cons(makeRational v, lq);
				lq;
			}
		}
	}

	if R has UnivariateGcdRing then {
		gcdUP(P:UnivariatePolynomialCategory0 %):(P,P)->P == {
			import from R,
			      UnivariateFreeAlgebraOverQuotient(R, PR, P0, P);
			gcdP := gcdUP PR;
			(p:P, q:P):P +-> {
				zero? p => q; zero? q => p;
				(d, pp) := makeIntegral p;
				(d, qq) := makeIntegral q;
				(d, g) := normalize gcdP(pp, qq);
				g;
			}
		}

		gcdquoUP(P:UnivariatePolynomialCategory0 %):(P,P)->(P,P,P) == {
			import from R,
			      UnivariateFreeAlgebraOverQuotient(R,PR,P0,P);
			gcdP := gcdquoUP PR;
			(p:P, q:P):(P,P,P) +-> {
				zero? p => (q, 0, 1);
				zero? q => (p, 1, 0);
				(dp, pp) := makeIntegral p;
				(dq, qq) := makeIntegral q;
				(gg, yy, zz) := gcdP(pp, qq);
				(a, g) := normalize gg;
				(g, (a / dp) * yy, (a / dq) * zz);
			}
		}
	}

	if R has RationalRootRing then {
		macro RR == RationalRoot;

		integerRoots(P:UnivariatePolynomialCategory0 %):P->List RR == {
			import from R;
			roots(P, integerRoots(PR)$R);
		}

		rationalRoots(P:UnivariatePolynomialCategory0 %):P->List RR == {
			import from R;
			roots(P, rationalRoots(PR)$R);
		}

		local roots(P:UnivariatePolynomialCategory0 %, _
				rootP: PR -> List RR):P -> List RR == {
			(p:P):List RR +-> {
			import from Integer,
			      UnivariateFreeAlgebraOverQuotient(R, PR, P0, P);
				ASSERT(~zero? p);
				zero? degree p => empty();
				(d, pp) := makeIntegral p;
				rootP pp;
			}
		}
	}

	if R has FactorizationRing then {
		factor(P:UnivariatePolynomialCategory0 %):P->(%, Product P) == {
			import from R,
			      UnivariateFreeAlgebraOverQuotient(R, PR, P0, P);
			fact := factor PR;
			(p:P):(%, Product P) +-> {
				(d, pp) := makeIntegral p;
				(lc, prod) := fact pp;
				(c, q) := normalize(P, prod);
				(c * lc / d, q);
			}
		}

		-- returns (c, q) s.t p = c q
		local normalize(P:UnivariatePolynomialCategory0 %,
				p:Product PR):(R, Product P) == {
			import from R,
			      UnivariateFreeAlgebraOverQuotient(R, PR, P0, P);
			c:R := 1;
			q:Product P := 1;
			for term in p repeat {
				(r, e) := term;
				(a, s) := normalize r;	-- r = a s, s monic
				q := times!(q, s, e);
				c := times!(c, a^e);
			}
			(c, q);
		}
	}
	}
}		

