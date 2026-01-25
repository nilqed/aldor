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
------------------------------ FF2GE.as ------------------------------------
#include "sumit"

#if ASDOC
\thistype{TwoStepFractionFreeGaussElimination}
\History{Thom Mulders}{8 July 96}{created}
\Usage{import from \this(R,M)}
\Params{
{\em R} & IntegralDomain & A coefficient ring\\
{\em M} & MatrixCategory0 R& A matrix type over R\\
}
\begin{exports}
\category{EliminationCategory(R,M)}\\
\end{exports}
\Descr{
This domain implements two-step fraction-free Gaussian elimination on matrices.
}
#endif

macro SI == SingleInteger;
macro Z == Integer;
macro ARR == PrimitiveArray SI;
macro B == Boolean;
macro V == Vector R;

TwoStepFractionFreeGaussElimination(R:IntegralDomain, M:MatrixCategory0 R):
   EliminationCategory(R,M) == add {

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

		c1:SI := 1;
		r:SI := 1;
		divisor:R := 1;

		while r<=n and c1<=ma repeat {
			l := pivot1(a,n,p,c1,r);
			if l<=n then {
				if l~=r then {
					temp := p(l);
					p(l) := p(r);
					p(r) := temp;
					d := -d;
				}
				st(r) := c1;
				if r<n then {
					c2 := c1+1;
					while c2<=ma repeat {
						k := pivot2(a,n,p,c1,c2,r);
						if k<=n then {
							if k~=r+1 then {
								temp := p(k);
								p(k) := p(r+1);
								p(r+1) := temp;
								d := -d;
							}
							st(r+1) := c2;
							cc0 := divDiffProd(a(p(r),c1), a(p(r+1),c2), a(p(r),c2), a(p(r+1),c1), divisor);
							for i in r+2..n repeat {
								cc1 := divDiffProd(a(p(i),c1), a(p(r),c2), a(p(r),c1), a(p(i),c2), divisor);
								cc2 := divDiffProd(a(p(r+1),c1), a(p(i),c2), a(p(i),c1), a(p(r+1),c2),divisor);
								for j in c2+1..ma repeat
										a(p(i),j) := divSumProd(cc0, a(p(i),j), cc1, a(p(r+1),j), cc2, a(p(r),j), divisor);
								for j in 1..mb repeat
										b(p(i),j) := divSumProd(cc0, b(p(i),j), cc1, b(p(r+1),j), cc2, b(p(r),j), divisor);
							}
							for j in c2+1..ma repeat
								a(p(r+1),j) := divDiffProd(a(p(r),c1), a(p(r+1),j), a(p(r+1),c1), a(p(r),j), divisor);
							for j in 1..mb repeat
								b(p(r+1),j) := divDiffProd(a(p(r),c1), b(p(r+1),j), a(p(r+1),c1), b(p(r),j), divisor);
							a(p(r+1),c2) := cc0;
							divisor := a(p(r+1),c2);
							r := r+2;
							c1 := c2+1;
							break;
						}
						else c2 := c2+1;
					}
					if c2>ma then {
						for i in r+1..n repeat {
							for j in 1..mb repeat
								b(p(i),j) := divDiffProd(a(p(r),c1), b(p(i),j), a(p(i),c1), b(p(r),j), divisor);
						}
						r := r+1;
						c1 := ma+1;
					}
				}
				else {
					r := r+1;
					c1 := c1+1;
				}
			}
			else c1 := c1+1;
		}
		(p,r-1,st,d);
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
		for i in 1..r repeat
			den(i) := a(p(i),st(i));
		den;
	}

	deter(a:M,p:ARR,r:SI,st:ARR,d:SI): R == {
		n := rows a;
		ASSERT(n=cols a);
		r<n => 0;
		d=1 => a(p(r),r);
		-a(p(r),r);
	}

	dependence(gen:Generator V,n:SI): (M,ARR,SI,R) == {
		import from B;
		a:M := zero(n,n+1);
		p:ARR := new n;
		for i in 1..n repeat p(i) := i;
		r:SI := 1;
		independent:B := true;
		while independent for v in gen repeat {
			for i in 1..n repeat
				a(i,r) := v(i);
			divisor:R := 1;
			for j in 1..r-1 by 2 repeat {
				c0 := a(p(j+1),j+1);
				for i in j+2..n repeat {
					a(p(i),r) := divSumProd(c0, a(p(i),r), _
							a(p(i),j), a(p(j+1),r), _
							a(p(i),j+1), a(p(j),r), _
							divisor);
				}
				a(p(j+1),r) := divDiffProd(a(p(j),j), a(p(j+1),r), _
						a(p(j+1),j), a(p(j),r), divisor);
				divisor := a(p(j+1),j+1);
			}
			l := pivot1(a,n,p,r,r);
			if l=n+1 then {
				independent := false;
				iterate;
			}
			if l~=r then {
				temp:=p(l);
				p(l):=p(r);
				p(r):=temp;
			}
			step!(gen);
			w := value(gen);
			for i in 1..n repeat
				a(i,r+1) := w(i);
			divisor:R := 1;
			for j in 1..r-1 by 2 repeat {
				c0 := a(p(j+1),j+1);
				for i in j+2..n repeat {
					a(p(i),r+1):=divSumProd(c0, a(p(i),r+1), _
						a(p(i),j), a(p(j+1),r+1), _
						a(p(i),j+1), a(p(j),r+1), _
						divisor);
				}
				a(p(j+1),r+1):=divDiffProd(a(p(j),j), a(p(j+1),r+1), _
					a(p(j+1),j), a(p(j),r+1), divisor);
				divisor := a(p(j+1),j+1);
			}
			k := pivot2(a,n,p,r,r+1,r);
			if k=n+1 then {
				r := r+1;
				independent := false;
				iterate;
			}
			if k~=r+1 then {
				temp:=p(k);
				p(k):=p(r+1);
				p(r+1):=temp;
			}
			c0 := divDiffProd(a(p(r),r), a(p(r+1),r+1), a(p(r+1),r), _
						a(p(r),r+1), divisor);
			for j in r+2..n repeat {
				c1 := divDiffProd(a(p(j),r), a(p(r),r+1), a(p(r),r), _
						a(p(j),r+1), divisor);
				c2:=divDiffProd(a(p(r+1),r), a(p(j),r+1), a(p(j),r), _
						a(p(r+1),r+1), divisor);
				a(p(j),r) := c1;
				a(p(j),r+1) := c2;
			}
			a(p(r+1),r+1) := c0;
			r := r+2;
		}
		(a,p,r,a(p(r-1),r-1));
	}

	local euclidean?:Boolean == R has SumitEuclideanDomain;

	local pivot1(a:M,n:SI,p:ARR,c:SI,r:SI): SI == {
		euclidean? => pivot1euclidean(a,n,p,c,r);
		pivot1general(a,n,p,c,r);
	}

	local pivot1general(a:M,n:SI,p:ARR,c:SI,r:SI): SI == {
		import from R;
		l := r;
		while (l<=n and a(p(l),c)=0) repeat l := l+1;
		l;
	}

	if R has SumitEuclideanDomain then {
		local pivot1euclidean(a:M,n:SI,p:ARR,c:SI,r:SI): SI == {
			import from R,Z;
			l := r;
			while (l<=n and a(p(l),c)=0) repeat l := l+1;
			for ll in l+1..n repeat
				if a(p(ll),c)~=0 and euclideanSize(a(p(ll),c))<euclideanSize(a(p(l),c)) then l := ll;
			l;
		}
	}

	local pivot2(a:M,n:SI,p:ARR,c1:SI,c2:SI,r:SI): SI == {
		euclidean? => pivot2euclidean(a,n,p,c1,c2,r);
		pivot2general(a,n,p,c1,c2,r);
	}

	local pivot2general(a:M,n:SI,p:ARR,c1:SI,c2:SI,r:SI): SI == {
		import from R;
		k := r+1;
		while (k<=n and a(p(r),c1)*a(p(k),c2)-a(p(k),c1)*a(p(r),c2)=0) repeat
				k := k+1;
		k;
	}

	if R has SumitEuclideanDomain then {
		local pivot2euclidean(a:M,n:SI,p:ARR,c1:SI,c2:SI,r:SI): SI == {
			import from R,Z;
			k := r;
			d:R := 0;
			while k<n and d=0 repeat {
				k := k+1;
				d := a(p(r),c1)*a(p(k),c2)-a(p(k),c1)*a(p(r),c2);
			}
			if d=0 then return(n+1);
			minsize := euclideanSize(d);
			mini := k;
			while k<n repeat {
				k := k+1;
				d := a(p(r),c1)*a(p(k),c2)-a(p(k),c1)*a(p(r),c2);
				s := euclideanSize(d);
				if d~=0 and s<minsize then {
					mini := k;
					minsize := s
				}
			};
			mini;
		}
	}
}


