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
------------------------ sit_qotbyct.as ---------------------------
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	B == Boolean;
	I == MachineInteger;
	Z == Integer;
	PR == DenseUnivariatePolynomial R;
	MR == DenseMatrix R;
	ARR == Array;
	V == Vector;
	P0 == % pretend FractionByCategory0 R;
	POL == UnivariatePolynomialCategory0;
}

#if ALDOC
\thistype{FractionByCategory}
\History{Manuel Bronstein}{9/6/98}{created}
\Usage{\this~R: Category}
\Params{ {\em R} & \astype{IntegralDomain} & an integral domain\\ }
\Descr{
\this(R) is the category of fractions of the integral domain {\em R} by
some nonzero nonunit $p \in R$,
\ie the set of all fractions whose denominator is a power of {\em p}.
}
\begin{exports}
\category{\astype{FractionByCategory0} R}\\
\end{exports}
#endif

define FractionByCategory(R:IntegralDomain): Category ==
	FractionByCategory0 R with {
	default {
	local sum(v:V Z):Z == {
		s:Z := 0;
		for x in v repeat s := add!(s, x);
		s;
	}

	local rgen(g:Generator V %, v:V Z):Generator V R == generate {
		import from I, VectorOverFraction(R, P0);
		for w in g for j in 1.. repeat {
			(mu, ww) := makeIntegralBy w;
			v.j := mu;
			yield ww;
		}
	}

	linearDependence(g:Generator V %, n:I):V % == {
		import from LinearAlgebra(R, MR);
		import from Z, V Z, R, V R, VectorOverFraction(R, P0);
		v:V Z := zero next n;
		dep := firstDependence(rgen(g, v), n);
		zero?(m := #dep) => makeRational dep;
		w:V % := zero m;
		-- TEMPORARY: MAY NEED SOME NORMALIZATION
		for i in 1..m repeat w.i := shift((dep.i)::%, v.i);
		w;
	}

	local psol(M:MatrixCategory %):(V Z,V Z,MR,V R) -> (M, V %) == {
		import from I, Z, B, R, VectorOverFraction(R, P0),
			MatrixCategoryOverFraction(R, MR, P0, M);
		(da:V Z, db:V Z, s:MR, d:V R):(M, V %) +-> {
			sl := makeRational s;
			(n, m) := dimensions sl;
			assert(m=#d); assert(n=#da); assert(n=#db);
			for j in 1..m | ~zero?(d.j) repeat {
				for i in 1..n repeat
					sl(i,j) := shift(sl(i, j), _
							da.j - db.j);
			}
			-- TEMPORARY: MAY NEED SOME NORMALIZATION
			(sl, makeRational d);
		}
	}

	solve(M:MatrixCategory %):(M, M) -> (M, M, V %) == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		psl := psol M;
		(a:M, b:M):(M, M, V %) +-> {
			(mua, ma) := makeRowIntegralBy a;
			(mub, mb) := makeRowIntegralBy b;
			(k, s, d) := solve(ma, mb);
			(sol, dd) := psl(mua, mub, s, d);
			-- TEMPORARY: MAY NEED SOME NORMALIZATION
			(makeRational k, sol, dd);
		}
	}

	particularSolution(M:MatrixCategory %):(M, M) -> (M, V %) == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		psl := psol M;
		(a:M, b:M):(M, V %) +-> {
			(mua, ma) := makeRowIntegralBy a;
			(mub, mb) := makeRowIntegralBy b;
			(s, d) := particularSolution(ma, mb);
			psl(mua, mub, s, d);
		}
	}

	invertibleSubmatrix(M:MatrixCategory %):M->(B,ARR I,ARR I) == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):(B, ARR I, ARR I) +-> {
			(mu, mr) := makeRowIntegralBy m;
			invertibleSubmatrix mr;
		}
	}

	maxInvertibleSubmatrix(M:MatrixCategory %):M->(ARR I,ARR I) == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):(ARR I, ARR I) +-> {
			(mu, mr) := makeRowIntegralBy m;
			maxInvertibleSubmatrix mr;
		}
	}

	inverse(M:MatrixCategory %):M -> (M, V %) == {
		import from Z, V Z, LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		psl := psol M;
		(m:M):(M, V %) +-> {
			(mu, mr) := makeRowIntegralBy m;
			(m1, d) := inverse mr;
			psl(mu, zero(#mu), m1, d);
		}
	}

	factorOfDeterminant(M:MatrixCategory %):M -> (B, %) == {
		import from Z, LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):(B, %) +-> {
			(mu, mr) := makeRowIntegralBy m;
			(det?, d) := factorOfDeterminant mr;
			(det?, shift(d::%, - sum mu));
		}
	}

	determinant(M:MatrixCategory %):M -> % == {
		import from Z, LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):% +-> {
			(mu, mr) := makeRowIntegralBy m;
			shift(determinant(mr)::%, - sum mu);
		}
	}

	rankLowerBound(M:MatrixCategory %):M -> (B, I) == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):(B, I) +-> {
			(mu, mr) := makeRowIntegralBy m;
			rankLowerBound mr;
		}
	}

	rank(M:MatrixCategory %):M -> I == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):I +-> {
			(mu, mr) := makeRowIntegralBy m;
			rank mr;
		}
	}

	span(M:MatrixCategory %):M -> ARR I == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):ARR I +-> {
			(mu, mr) := makeRowIntegralBy m;
			span mr;
		}
	}

	kernel(M:MatrixCategory %):M -> M == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):M +-> {
			(mu, mr) := makeRowIntegralBy m;
			-- TEMPORARY: MAY NEED SOME NORMALIZATION
			makeRational kernel mr;
		}
	}

	subKernel(M:MatrixCategory %):M -> (B, M) == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):(B, M) +-> {
			(mu, mr) := makeRowIntegralBy m;
			(ker?, k) := subKernel mr;
			-- TEMPORARY: MAY NEED SOME NORMALIZATION
			(ker?, makeRational k);
		}
	}

	if R has UnivariateGcdRing then {
		gcdUP(P:POL %):(P,P)->P == {
			import from R,
			     UnivariateFreeFiniteAlgebraOverFraction(R,PR,P0,P);
			gcdP := gcdUP PR;
			(r:P, q:P):P +-> {
				zero? r => q; zero? q => r;
				(d, pp) := makeIntegralBy r;
				(d, qq) := makeIntegralBy q;
				-- TEMPORARY: MAY NEED SOME NORMALIZATION
				makeRational gcdP(pp, qq);
			}
		}

		-- TEMPORARY: MUST DO BETTER
		gcd(a:%, b:%):% == never;
	}

	if R has RationalRootRing then {
		macro RR == FractionalRoot Z;

		integerRoots(P:POL %):P->Generator RR == {
			import from R;
			roots(P, integerRoots(PR)$R);
		}

		rationalRoots(P:POL %):P->Generator RR == {
			import from R;
			roots(P, rationalRoots(PR)$R);
		}

		local roots(P:POL %,rootP:PR->Generator RR):P->Generator RR == {
			(r:P):Generator RR +-> {
				import from Boolean, Z, List RR,
				     UnivariateFreeFiniteAlgebraOverFraction(R,_
								PR,P0,P);
				assert(~zero? r);
				zero? degree r => generator(empty$List(RR));
				(d, pp) := makeIntegralBy r;
				rootP pp;
			}
		}
	}

	if R has FactorizationRing then {
		factor(P:POL %):P->(%, Product P) == {
			import from R;
			factP := factor PR;
			(r:P):(%, Product P) +-> {
				import from Z,
				     UnivariateFreeFiniteAlgebraOverFraction(R,_
								PR,P0,P);
				zero? r or zero?(d := degree r) =>
					(leadingCoefficient r, 1);
				one? d => (1, term(r, 1));
				(mu, pp) := makeIntegralBy r;
				(s, prod) := factP pp;
				(shift(s::%, -mu), makeRational(P, prod));
			}
		}

		local makeRational(P:POL %,
					prod: Product PR):Product P == {
			import from R,
			     UnivariateFreeFiniteAlgebraOverFraction(R,PR,P0,P);
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
