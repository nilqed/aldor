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
------------------------ quotbycat.as ---------------------------
#include "sumit"

macro {
	I == SingleInteger;
	Z == Integer;
	PR == DenseUnivariatePolynomial R;
	MR == DenseMatrix R;
	ARR == PrimitiveArray;
}

#if ASDOC
\thistype{QuotientByCategory}
\History{Manuel Bronstein}{9/6/98}{created}
\Usage{\this~R: Category}
\Params{ {\em R} & IntegralDomain & an integral domain\\ }
\Descr{
\this(R) is the category of quotients of the integral domain {\em R} by
some nonzero nonunit $p \in R$,
\ie the set of all fractions whose denominator is a power of {\em p}.
}
\begin{exports}
\category{QuotientCategory R}\\
order: & \% $\to$ Integer & Valuation at p\\
shift: & (\%, Integer) $\to$ \% & Multiplication by a power of p\\
\end{exports}
#endif

QuotientByCategory(R: IntegralDomain): Category == QuotientCategory R with {
	order: % -> Z;
#if ASDOC
\aspage{order}
\Usage{\name~x}
\Signature{\%}{Integer}
\Params{ {\em x} & \% & A quotient by a power of p\\ }
\Retval{Returns $n$ such that $x = a p^n$ and $a \in R$, $p \nodiv a$.}
#endif
	shift: (%, Z) -> %;
#if ASDOC
\aspage{shift}
\Usage{\name(x, n)}
\Signature{(\%, Integer)}{\%}
\Params{
{\em x} & \% & A quotient by a power of p\\
{\em n} & Integer & An exponent\\
}
\Retval{Returns $x p^n$.}
#endif
	default {
	-- THOSE USE THE order FUNCTION, SO THEY ARE DIFFERENT FROM
	-- THE ONES IN ufalgquot.as AND matquot.as

	-- returns mu s.t. row(A, r) = p^-mu * row(B, r)
	local makeInt!(M:MatrixCategory0 %, B:M, r:I, A:MR):Z == {
		import from Z;
		c := cols B;
		ASSERT(c <= cols A); ASSERT(r <= rows A);
		mu:Z := 0;
		for j in 1..c repeat {
			b := B(r, j);
			if ~zero? b then {
				m:Integer := order(b)$%;
				if m < mu then mu := m;
			}
		}
		assert(mu <= 0);
		for j in 1..c repeat A(r, j) := numerator shift(B(r, j), -mu);
		mu;
	}

	-- returns (mu, A) s.t. each row of A is a multiple of the
	-- corresponding row of B, and det(B) = p^mu det(A)
	local makeInt(M:MatrixCategory0 %, B:M):(Z, MR) == {
		import from I, Z;
		(r, c) := dimensions B;
		A:MR := zero(r, c);
		mu:Z := 0;
		for i in 1..r repeat mu := mu + makeInt!(M, B, i, A);
		(mu, A);
	}

	-- returns (n, q) s.t. r = p^n q
	local makeInt(P:UnivariatePolynomialCategory0 %, r:P):(Z, PR) == {
		import from List %;
		mu:Z := 0;
		for c in coefficients r repeat {
			m:Integer := order(c)$%;
			if m < mu then mu := m;
		}
		q:PR := 0;
		for term in r repeat {
			(c, n) := term;
			q := add!(q, numerator shift(c, -mu), n);
		}
		(mu, q);
	}

	if R has LinearAlgebraRing then {
		determinant(M:MatrixCategory0 %):M -> % == {
			import from R, MR,
				MatrixCategoryOverQuotient(R, MR, %, M);
			detR := determinant MR;
			(m:M):% +-> {
				(mu, mr) := makeInt(M, m);
				shift(detR(mr)::%, mu);
			}
		}

		rank(M:MatrixCategory0 %):M -> I == {
			import from R, MR,
				MatrixCategoryOverQuotient(R, MR, %, M);
			rankR := rank MR;
			(m:M):I +-> {
				(mu, mr) := makeInt(M, m);
				rankR mr;
			}
		}

		span(M:MatrixCategory0 %):M -> (I, ARR I) == {
			import from R, MR,
				MatrixCategoryOverQuotient(R, MR, %, M);
			spanR := span MR;
			(m:M):(I, ARR I) +-> {
				(mu, mr) := makeInt(M, m);
				spanR mr;
			}
		}

		nullSpace(M:MatrixCategory0 %):M -> List Vector % == {
			import from R,MR,List Vector R,VectorOverQuotient(R,%);
			nullR := nullSpace MR;
			(m:M):List Vector % +-> {
				(mu, mr) := makeInt(M, m);
				lr := nullR mr;
				lq:List Vector % := empty();
				-- TEMPORARY: MAY NEED SOME NORMALIZATION
				for v in lr repeat
					lq := cons(makeRational v, lq);
				lq;
			}
		}
	}

	if R has UnivariateGcdRing then {
		gcdUP(P:UnivariatePolynomialCategory0 %):(P,P)->P == {
			import from R,
				UnivariateFreeAlgebraOverQuotient(R, PR, %, P);
			gcdP := gcdUP PR;
			(r:P, q:P):P +-> {
				zero? r => q; zero? q => r;
				(d, pp) := makeInt(P, r);
				(d, qq) := makeInt(P, q);
				-- TEMPORARY: MAY NEED SOME NORMALIZATION
				makeRational gcdP(pp, qq);
			}
		}

		-- TEMPORARY: MUST DO BETTER
		gcd(a:%, b:%):% == a;
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
			(r:P):List RR +-> {
				import from Integer;
				ASSERT(~zero? r);
				zero? degree r => empty();
				(d, pp) := makeInt(P, r);
				rootP pp;
			}
		}
	}

	if R has FactorizationRing then {
		factor(P:UnivariatePolynomialCategory0 %):P->(%, Product P) == {
			import from R;
			factP := factor PR;
			(r:P):(%, Product P) +-> {
				import from Integer;
				zero? r or zero?(d := degree r) =>
					(leadingCoefficient r, 1);
				one? d => (1, term(r, 1));
				(mu, pp) := makeInt(P, r);
				(s, prod) := factP pp;
				(shift(s::%, mu), makeRational(P, prod));
			}
		}

		local makeRational(P:UnivariatePolynomialCategory0 %,
					prod: Product PR):Product P == {
			import from R,
				UnivariateFreeAlgebraOverQuotient(R, PR, %, P);
			c:R := 1;
			q:Product P := 1;
			for term in prod repeat {
				(r, e) := term;
				q := times!(q, makeRational r, e);
			}
			q;
		}
	}
	}		
}
