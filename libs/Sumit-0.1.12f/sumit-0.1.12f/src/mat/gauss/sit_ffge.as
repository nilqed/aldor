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
---------------------------- sit_ffge.as ------------------------------------
-- Copyright (c) Thom Mulders 1996
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1996
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I == MachineInteger;
	ARR == PrimitiveArray;
	Sn == Permutation n;
}

#if ALDOC
\thistype{FractionFreeGaussElimination}
\History{Thom Mulders}{8 July 96}{created}
\Usage{import from \this(R,M)}
\Params{
{\em R} & \astype{IntegralDomain} & A coefficient ring\\
{\em M} & \astype{MatrixCategory} R & A matrix type over R\\
}
\begin{exports}
\category{\astype{LinearEliminationCategory}(R,M)}\\
\end{exports}
\Descr{
This domain implements fraction--free Gaussian elimination on matrices.
}
#endif

FractionFreeGaussElimination(R:IntegralDomain, M:MatrixCategory R):
	LinearEliminationCategory(R, M) == add {

	rowEchelon!(a:M,b:M):(I->I,I,ARR I,I) == rowEch!(a,b,numberOfRows a);

	local rowEch!(a:M, b:M, n:I): (I->I,I,ARR I,I) == {

		import from R, Sn;

		TRACE("FFGE::rowEch!, n = ", n);

		ma := numberOfColumns a; mb := numberOfColumns b;
		assert(n=numberOfRows b);
		p:Sn := 1;
		st:ARR I := new(next n, next ma);       -- ignore st(0)

		r:I := 1;
		divisor:R := 1;
		while r<=n for c in 1..ma repeat {
			l := pivot(a, mapping p, c, r);
			TRACE("FFGE::rowEch!, pivot = ", l);
			if l<=n then {
				st(r) := c;
				p := transpose!(p, l, r);
				arc:=a(p(r),c);
				for i in next r..n repeat {
					aic := a(p(i),c);
					for j in next c..ma repeat
						a(p(i),j) := divDiffProd(arc, _
							a(p(i),j), aic, a(p(r),_
							j), divisor);
					for j in 1..mb repeat
						b(p(i),j) := divDiffProd(arc, _
							b(p(i),j), aic, b(p(r),_
							j), divisor);
				}
				r := next r;
				divisor := arc;
			}
		}
		TRACE("FFGE::rowEch!, rank = ", r - 1);
		TRACE("FFGE::rowEch!, sign p = ", sign p);
		(mapping p, prev r,st,sign p);
	}

	denominators(a:M,p:I->I,r:I,st:ARR I): ARR R == {
		den:ARR R := new(next r);	-- ignore den.0
		for i in 1..r repeat den(i) := a(p(i),st(i));
		den;
	}

	deter(a:M,p:I->I,r:I,d:I): R == {
		n := numberOfRows a;
		assert(n=numberOfColumns a);
		r<n => 0;
		d=1 => a(p(r),r);
		-a(p(r),r);
	}

	dependence(gen:Generator Vector R,n:I): (M,I->I,I,R) == {
		import from Boolean, Vector R, Sn;
		TRACE("FFGE::dependence, n = ", n);
		a:M := zero(n,n+1);
		p:Sn := 1;
		r:I := 1;
		independent := true;
		while independent for v in gen repeat {
			TRACE("FFGE::dependence, r = ", r);
			for i in 1..n repeat a(i,r) := v(i);
			divisor:R := 1;
			for j in 1..prev r repeat {
				ajj := a(p(j),j);
				for i in next(j)..n repeat {
					TRACE("FFGE::dependence, i = ", i);
					a(p(i),r) := divDiffProd(ajj,a(p(i),r),_
						a(p(i),j), a(p(j),r), divisor);
				};
				divisor := ajj;
			}
			l := pivot(a, mapping p, r, r);
			independent := l <= n;
			if independent then {
				p := transpose!(p, l, r);
				r := next r;
			}
		}
		TRACE("FFGE::dependence, r = ", r);
		(a, mapping p, r, a(p(prev r), prev r));
	}
}

