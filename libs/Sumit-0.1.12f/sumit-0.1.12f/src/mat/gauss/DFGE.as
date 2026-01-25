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
------------------------------ DFGE.as ------------------------------------
#include "sumit"

#if ASDOC
\thistype{DivisionFreeGaussElimination}
\History{Thom Mulders}{8 July 96}{created}
\Usage{import from \this(R,M)}
\Params{
{\em R} & CommutativeRing & A coefficient ring\\
{\em M} & MatrixCategory0 R& A matrix type over R\\
}
\begin{exports}
\category{EliminationCategory(R,M)}\\
\end{exports}
\Descr{
This domain implements division-free Gaussian elimination on matrices.
}
#endif

macro SI == SingleInteger;
macro ARR == PrimitiveArray SI;
macro B == Boolean;
macro V == Vector R;

DivisionFreeGaussElimination(R:CommutativeRing, M:MatrixCategory0 R): EliminationCategory(R,M) == add {

	local rowEch!(a:M,b:M): (ARR,SI,ARR,SI) == {

		import from R;

		n := rows a;
		ASSERT(n=rows b);
		ma := cols a;
		mb := cols b;
		d:SI := 1;
		p:ARR := new(n);
		for i in 1..n repeat p(i) := i;
		st:ARR := new(n, next ma);

		c:SI := 1;
		r:SI := 1;

		while r<=n and c<=ma repeat {
			l := pivot(a,n,p,c,r);
			if l<=n then {
				st(r) := c;
				if l~=r then {
					temp := p(l);
					p(l) := p(r);
					p(r) := temp;
					d:=-d;
				}
				arc:=a(p(r),c);
				for i in r+1..n repeat {
					aic := a(p(i),c);
					for j in c+1..ma repeat
						a(p(i),j):=arc*a(p(i),j)-aic*a(p(r),j);
					for j in 1..mb repeat
						b(p(i),j):=arc*b(p(i),j)-aic*b(p(r),j);
				}
				r := r+1;
			}
			c := c+1;
		}
		(p,r-1,st,d);
	}

	local pivot(a:M,n:SI,p:ARR,c:SI,r:SI): SI == {
		import from R;
		l := r;
		while (l<=n and a(p(l),c)=0) repeat l := l+1;
		l;
	}

	rowEchelon!(a:M): (ARR,SI,ARR,SI) ==
		rowEch!(a,zero(rows a,0));

	extendedRowEchelon!(a:M): (ARR,SI,ARR,SI,M) == {
		b := one rows a;
		(p,r,st,d) := rowEch!(a,b);
		(p,r,st,d,b);
	}

	denominators(a:M,p:ARR,r:SI,st:ARR): PrimitiveArray R == {
		den:PrimitiveArray R := new(r);
		q1:R := 1;
		q2:R := 1;
		for i in 1..min(2,r) repeat
			den(i) := a(p(i),st(i));
		for i in min(2,r)+1..r repeat {
			q1 := q1*a(p(i-2),st(i-2));
			q2 := q2*q1;
			den(i) := quotient(a(p(i),st(i)),q2);
		}
		den;
	}

	deter(a:M,p:ARR,r:SI,st:ARR,d:SI): R == {
		n := rows a;
		ASSERT(n=cols a);
		r<n => 0;
		{
			d=1 => det := a(p(r),r);
			det := -a(p(r),r);
		}
		q1:R := 1;
		q2:R := 1;
		for i in 1..r-2 repeat {
			q1 := q1*a(p(i),i);
			q2 := q2*q1;
		}
		quotient(det,q2);
	}

	dependence(gen:Generator V,n:SI): (M,ARR,SI,R) == {
		import from B;
		a:M := zero(n,n+1);
		p:ARR := new n;
		for i in 1..n repeat p(i) := i;
		r:SI := 1;
		independent:B := true;
		while independent for v in gen repeat {
			for i in 1..n repeat a(i,r) := v(i);
			for j in 1..r-1 repeat {
				ajj := a(p(j),j);
				for i in j+1..n repeat {
					a(p(i),r):=ajj*a(p(i),r)-a(p(i),j)*a(p(j),r);
				}
			}
			l := pivot(a,n,p,r,r);
			if l=n+1 then {
				independent := false;
				iterate
			} 
			if l~=r then {
				temp:=p(l);
				p(l):=p(r);
				p(r):=temp;
			}
			r := r+1;
		}
		q1:R := 1;
		q2:R := 1;
		for i in 1..r-3 repeat {
			q1 := q1*a(p(i),i);
			q2 := q2*q1;
		}
		(a,p,r,quotient(a(p(r-1),r-1),q2));
	}
}
