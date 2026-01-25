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
------------------------ sit_qotfcat.as ---------------------------
-- Copyright (c) Laurent Bernardin 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I   == MachineInteger;
	B   == Boolean;
	ARR == Array;
	V   == Vector;
	POL == UnivariatePolynomialCategory0;
}

#if ALDOC
\thistype{FractionFieldCategory}
\History{Laurent Bernardin}{1/12/94}{created}
\Usage{\this~R: Category}
\Params{ {\em R} & \astype{IntegralDomain} & an integral domain\\ }
\Descr{\this~R is the category of the fraction fields of R.}
\begin{exports}
\category{\astype{FractionFieldCategory0} R}\\
\end{exports}
#endif

define FractionFieldCategory(R:IntegralDomain): Category ==
	FractionFieldCategory0 R with {
	default {
	macro {
		MR == DenseMatrix R;
		PR == DenseUnivariatePolynomial R;
		P0 == % pretend FractionFieldCategory0 R;
	}

	local prod(v:V R):R == {
		p:R := 1;
		for x in v repeat p := times!(p, x);
		p;
	}

	local rgen(g:Generator V %, v:V R):Generator V R == generate {
		import from I, VectorOverFraction(R, P0);
		for w in g for j in 1.. repeat {
			(d, ww) := makeIntegral w;
			v.j := d;
			yield ww;
		}
	}

	linearDependence(g:Generator V %, n:I):V % == {
		import from R, V R,VectorOverFraction(R,P0),LinearAlgebra(R,MR);
		v:V R := zero next n;
		dep := firstDependence(rgen(g, v), n);
		zero?(m := #dep) => makeRational dep;
		a := v.1 * dep.1;
		w:V % := zero m;
		w.1 := 1;
		for i in 2..m repeat w.i := (v.i * dep.i) / a;
		w;
	}

	local psol(M:MatrixCategory %):(V R,V R,MR,V R) -> (M, V %) == {
		import from I,B,R,MatrixCategoryOverFraction(R,MR,P0,M);
		(da:V R, db:V R, s:MR, d:V R):(M, V %) +-> {
			sl := makeRational s;
			(n, m) := dimensions sl;
			assert(m=#d); assert(n=#da); assert(n=#db);
			dd:V % := zero m;
			ab:V % := zero n;
			for i in 1..n repeat ab.i := da.i / db.i;
			for j in 1..m | ~zero?(d.j) repeat {
				dd.j := 1;
				dj := (d.j)::%;
				for i in 1..n repeat
					sl(i,j) := (ab.i/dj) * sl(i,j);
			}
			(sl, dd);
		}
	}

	solve(M:MatrixCategory %):(M, M) -> (M, M, V %) == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		psl := psol M;
		(a:M, b:M):(M, M, V %) +-> {
			(da, ma) := makeRowIntegral a;
			(db, mb) := makeRowIntegral b;
			(k, s, d) := solve(ma, mb);
			(sol, dd) := psl(da, db, s, d);
			(makeRational k, sol, dd);
		}
	}

	particularSolution(M:MatrixCategory %):(M, M) -> (M, V %) == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		psl := psol M;
		(a:M, b:M):(M, V %) +-> {
			(da, ma) := makeRowIntegral a;
			(db, mb) := makeRowIntegral b;
			(s, d) := particularSolution(ma, mb);
			psl(da, db, s, d);
		}
	}

	invertibleSubmatrix(M:MatrixCategory %):M->(B,ARR I,ARR I) == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):(B, ARR I, ARR I) +-> {
			(denoms, mr) := makeRowIntegral m;
			invertibleSubmatrix mr;
		}
	}

	maxInvertibleSubmatrix(M:MatrixCategory %):M->(ARR I,ARR I) == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):(ARR I, ARR I) +-> {
			(denoms, mr) := makeRowIntegral m;
			maxInvertibleSubmatrix mr;
		}
	}

	inverse(M:MatrixCategory %):M -> (M, V %) == {
		import from R, V R, LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		psl := psol M;
		(m:M):(M, V %) +-> {
			(denoms, mr) := makeRowIntegral m;
			(m1, d) := inverse mr;
			psl(denoms, new(#denoms, 1), m1, d);
		}
	}

	factorOfDeterminant(M:MatrixCategory %):M -> (B, %) == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):(B, %) +-> {
			(denoms, mr) := makeRowIntegral m;
			(det?, d) := factorOfDeterminant mr;
			(det?, d / prod(denoms));
		}
	}

	determinant(M:MatrixCategory %):M -> % == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):% +-> {
			(denoms, mr) := makeRowIntegral m;
			determinant(mr) / prod(denoms);
		}
	}

	rankLowerBound(M:MatrixCategory %):M -> (B, I) == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):(B, I) +-> {
			(denoms, mr) := makeRowIntegral m;
			rankLowerBound mr;
		}
	}

	rank(M:MatrixCategory %):M -> I == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):I +-> {
			(denoms, mr) := makeRowIntegral m;
			rank mr;
		}
	}

	span(M:MatrixCategory %):M -> ARR I == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):ARR I +-> {
			(denoms, mr) := makeRowIntegral m;
			span mr;
		}
	}

	kernel(M:MatrixCategory %):M -> M == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):M +-> {
			(denoms, mr) := makeRowIntegral m;
			makeRational kernel mr;
		}
	}

	subKernel(M:MatrixCategory %):M -> (B, M) == {
		import from LinearAlgebra(R, MR);
		import from MatrixCategoryOverFraction(R, MR, P0, M);
		(m:M):(B, M) +-> {
			(denoms, mr) := makeRowIntegral m;
			(ker?, k) := subKernel mr;
			(ker?, makeRational k);
		}
	}

	if R has UnivariateGcdRing then {
		gcdUP(P:POL %):(P,P)->P == {
			import from R,
			     UnivariateFreeFiniteAlgebraOverFraction(R,PR,P0,P);
			gcdP := gcdUP PR;
			(p:P, q:P):P +-> {
				zero? p => q; zero? q => p;
				(d, pp) := makeIntegral p;
				(d, qq) := makeIntegral q;
				(d, g) := normalize gcdP(pp, qq);
				g;
			}
		}

		gcdquoUP(P:POL %):(P,P)->(P,P,P) == {
			import from R,
			     UnivariateFreeFiniteAlgebraOverFraction(R,PR,P0,P);
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
		macro RR == FractionalRoot Integer;

		integerRoots(P:POL %):P -> Generator RR == {
			import from R;
			roots(P, integerRoots(PR)$R);
		}

		rationalRoots(P:POL %):P -> Generator RR == {
			import from R;
			roots(P, rationalRoots(PR)$R);
		}

		local roots(P:POL %,rootP:PR->Generator RR):P->Generator RR == {
			(p:P):Generator RR +-> {
			import from Integer, B, List RR,
			     UnivariateFreeFiniteAlgebraOverFraction(R,PR,P0,P);
				assert(~zero? p);
				zero? degree p => generator(empty$List(RR));
				(d, pp) := makeIntegral p;
				rootP pp;
			}
		}
	}

	if R has FactorizationRing then {
		factor(P:POL %):P->(%, Product P) == {
			import from R,
			     UnivariateFreeFiniteAlgebraOverFraction(R,PR,P0,P);
			fact := factor PR;
			(p:P):(%, Product P) +-> {
				(d, pp) := makeIntegral p;
				(lc, pr) := fact pp;
				(c, q) := normalize(P, pr);
				(c * lc / d, q);
			}
		}

		-- returns (c, q) s.t p = c q
		local normalize(P:POL %, p:Product PR):(R, Product P) == {
			import from R,
			     UnivariateFreeFiniteAlgebraOverFraction(R,PR,P0,P);
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

