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
------------------------------ Hermite.as ------------------------------------
#include "sumit"

#if ASDOC
\thistype{HermiteGaussElimination}
\History{Thom Mulders}{8 July 96}{created}
\Usage{import from \this(R,M)}
\Params{
{\em R} & SumitEuclideanDomain & A coefficient ring\\
{\em M} & MatrixCategory0 R& A matrix type over R\\
}
\begin{exports}
\category{EliminationCategory(R,M)}\\
\end{exports}
\Descr{
This domain implements Hermite reduction on matrices.
}
#endif

macro SI == SingleInteger;
macro ARR == PrimitiveArray SI;
macro B == Boolean;
macro V == Vector R;

HermiteGaussElimination(R:SumitEuclideanDomain, M:MatrixCategory0 R): EliminationCategory(R,M) == add {

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
					d := -d;
				}
				g := a(p(r),c);
				for i in r+1..n repeat {
					if a(p(i),c)=0 then iterate;
					(g,x,y) := extendedEuclidean(g,a(p(i),c));
					a1 := quotient(a(p(r),c),g);
					b1 := quotient(a(p(i),c),g);
					a(p(r),c) := g;
					for j in c+1..ma repeat {
						temp1 := a(p(r),j);
						a(p(r),j) := x*a(p(r),j)+y*a(p(i),j);
						a(p(i),j) := -b1*temp1+a1*a(p(i),j);
					}
					for j in 1..mb repeat {
						temp1 := b(p(r),j);
						b(p(r),j) := x*b(p(r),j)+y*b(p(i),j);
						b(p(i),j) := -b1*temp1+a1*b(p(i),j);
					}
				}
				q:R := 0;
				for i in 1..r-1 repeat {
					(q,rr) := divide!(a(p(i),c),g,q);
					a(p(i),c) := rr;
					for j in c+1..ma repeat
						a(p(i),j) := a(p(i),j)-q*a(p(r),j);
					for j in 1..mb repeat
						b(p(i),j) := b(p(i),j)-q*b(p(r),j);
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
		det:R := 1;
		for i in 1..r repeat {
			det := det*a(p(i),st(i));
			den(i) := det;
		}
		den;
	}

	deter(a:M,p:ARR,r:SI,st:ARR,d:SI): R == {
		n := rows a;
		ASSERT(n=cols a);
		r<n => 0;
		{
			d=1 => det:R := 1;
		 	det:R := -1;
		}
		for i in 1..r repeat
			det := det*a(p(i),i);
		det;
	}

	dependence(gen:Generator V,n:SI): (M,ARR,SI,R) == {
		import from B;
		a:M := zero(n,n+1);
		t:M := one n;
		p:ARR := new n;
		for i in 1..n repeat p(i) := i;
		r:SI := 1;
		independent:B := true;
		while independent for v in gen repeat {
			for i in 1..n repeat {
				e:R := 0;
				for k in 1..n repeat
					e := e+t(i,k)*v(k);
				a(i,r) := e;
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
			g := a(p(r),r);
			for i in r+1..n repeat {
				if a(p(i),r)=0 then iterate;
				(g,x,y) := extendedEuclidean(g,a(p(i),r));
				a1 := quotient(a(p(r),r),g);
				b1 := quotient(a(p(i),r),g);
				a(p(r),r) := g;
				a(p(i),r) := 0;
				for j in 1..n repeat {
					temp1 := t(p(r),j);
					t(p(r),j) := x*t(p(r),j)+y*t(p(i),j);
					t(p(i),j) := -b1*temp1+a1*t(p(i),j);
				}
			}
			q:R := 0;
			for i in 1..r-1 repeat {
				(q,rr) := divide!(a(p(i),r),g,q);
				a(p(i),r) := rr;
				for j in 1..n repeat
					t(p(i),j) := t(p(i),j)-q*t(p(r),j);
			}
			r:=r+1;
		}
		d:R := 1;
		for i in 1..r-1 repeat
			d := d*a(p(i),i);
		(a,p,r,d);
	}
}



