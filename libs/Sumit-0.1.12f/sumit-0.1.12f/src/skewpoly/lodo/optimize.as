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
------------------------------ optimize.as --------------------------------
#include "sumit"

macro SI == SingleInteger;
macro Z == Integer;
macro PA == PrimitiveArray;
macro ARR == PA SI;
macro DARR == PA PA SI;

#if ASDOC
\thistype{Optimize}
\History{Thom Mulders}{23 September 96}{created}
\Usage{import from \this(R,M)}
\Params{
{\em R} & SumitRing & A coefficient ring\\
{\em M} & MatrixCategory0 R& A matrix type over R\\
}
\Descr{\name~(R,M) provides ?????}
\begin{exports}
optimize: & (M,R $\to$ Partial SI) $\to$ (ARR,ARR,SI) & ?????\\
\end{exports}
\Aswhere{
Z & == & Integer\\
V & == & Vector Z\\
}
#endif

Optimize(R:SumitRing,M:MatrixCategory0 R): with {
	optimize: (M,R->Partial SI) -> (PA Z,PA Z,SI);
#if ASDOC
\aspage{optimize}
\Usage{\name(a,f)}
\Signature{(M,R $\to$ Partial Integer)}{(Vector Integer,Vector Integer,Integer)}
\Params{
{\em a} & M & A matrix\\
{\em f} & R $\to$ Partial Integer & A partial function from R to the Integers\\
}
\Descr{
???????????
}
#endif
} == add {
	optimize(a:M,f:R->Partial SI): (PA Z,PA Z,SI) ==
		linprog(applyFunction(a, f), rows a, cols a);

	-- Map f to a. If the value of f applied to an entry of a is 'failed'
	-- the corresponding value will be -1.
	local applyFunction(a:M,f:R->Partial SI): DARR == {
		import from Partial SI,SI;
		START__TIME;
		n := rows a;
		m := cols a;
		mat:DARR := new n;
		for i in 1..n repeat
			mat(i) := new m;
		for i in 1..n repeat
			for j in 1..m repeat {
				v := f(a(i,j));
				if failed? v then
					mat(i)(j) := -1;
				else
					mat(i)(j) := retract v;
		}
		TIME("optimize::time to create order matrix = ");
		mat;
	}

#if ASTRACE
	local trace(a:DARR, n:SI, m:SI):() == {
		for i in 1..n repeat {
			for j in 1..m repeat print << a(i)(j) << " ";
			print << newline;
		}
	}

	local trace(a:PA Z, n:SI):() == {
		for i in 1..n repeat print << a.i << " ";
		print << newline;
	}
#endif

-- a represents a matrix with SI coefficients. Vectors r and c with Integer
-- coefficients are computed such that
-- 1) r(i)+c(j)+a(i)(j)>=0 for all i,j
-- 2) sum(r(i)+c(j)+a(i)(j); i,j such that a(i)(j)>=0) is minimal
-- Also this minimal sum is returned.
-- In fact the dual linear programming problem is solved. By simulating the proces
-- of elimination on an identity matrix the actual solution is also found.
-- 
--  DESCRIPTION OF ALGORITHM
--  

-- The tableau of the dual problem has the following shape:
--
--  [ A  b I ]
--  [ -c

	local linprog(a:DARR,n:SI,m:SI): (PA Z,PA Z,SI) == {
		import from ARR, Z, PA Z;
		TRACE("optimize::linprog, n = ", n);
		TRACE("optimize::linprog, m = ", m);
#if ASTRACE
		trace(a, n, m);
#endif
		START__TIME;
		R:ARR := new(n,0);
		C:ARR := new(m,0);
		N:SI := 0;
		sum:SI := 0;
		for i in 1..n repeat
			for j in 1..m repeat 
				if a(i)(j) >= 0 then {
					sum := sum+a(i)(j);
					N := N+1;
					R(i) := R(i)+1;
					C(j) := C(j)+1;
				}
		TRACE("optimize::linprog, N = ", N);
		mat:DARR := new (n+m);
		for i in 1..n+m repeat
			mat(i) := new(N+n+m,0);
		TRACE("optimize::linprog, all mat(i) allocated", "");
		for i in 1..n+m-1 repeat
			mat(i)(N+1+i) := 1;
		for i in 2..n repeat
			mat(i-1)(N+1) := R(i);
		for j in 1..m repeat
			mat(n-1+j)(N+1) := C(j);
		ind:SI := 0;
		for j in 1..m repeat
			if a(1)(j) >=0 then {
				ind := ind+1;
				mat(n-1+j)(ind) := 1;
		}
		for i in 2..n repeat
			for j in 1..m repeat 
				if a(i)(j) >= 0 then {
					ind := ind+1;
					mat(i-1)(ind) := 1;
					mat(n-1+j)(ind) := 1;
				}
		base:ARR := new(n+m-1,0);
		(i0,j0) := pivot1(base,mat,n,m,N);
		while i0 ~= 0 repeat {
			base(i0) := j0;
			applyPivot!(mat,i0,j0,n+m-1,N+n+m);
			(i0,j0) := pivot1(base,mat,n,m,N);
		}
		(i0,j0) := pivot2(base,mat,n,m,N);
		while i0 ~= 0 repeat {
			base(i0) := j0;
			applyPivot!(mat,i0,j0,n+m-1,N+n+m);
			(i0,j0) := pivot2(base,mat,n,m,N);
		}
		ind := 0;
		for i in 1..n repeat
			for j in 1..m repeat
				if a(i)(j) >= 0 then {
					ind := ind+1;
					mat(n+m)(ind) := -a(i)(j);
				}
		for i in 1..n+m-1 repeat
			if base(i)>0 then {
				c := mat(n+m)(base(i));
				for j in 1..N+n+m repeat
					mat(n+m)(j) := mat(n+m)(j)-c*mat(i)(j)
			}
		(i0,j0) := pivot3(mat,n,m,N);
		while i0 ~= 0 repeat {
			applyPivot!(mat,i0,j0,n+m,N+n+m);
			(i0,j0) := pivot3(mat,n,m,N);
		}
		row:PA Z := new n;
		col:PA Z := new m;
		row(1) := 0;
		for i in 2..n repeat
			row(i) := (-mat(n+m)(N+i))::Z;
		for j in 1..m repeat
			col(j) := (-mat(n+m)(N+n+j))::Z;
		mincol:= col(1);
		for j in 2..m repeat
			if col(j)<mincol then
				mincol := col(j);
		for j in 1..m repeat
			col(j) := col(j)-mincol;
		for i in 1..n repeat
			row(i) := row(i)+mincol;
		TIME("optimize::time for linear programming = ");
#if ASTRACE
		trace(row, n);
		trace(col, m);
#endif
		(row,col,sum-mat(n+m)(N+1));
	}

	local pivot1(b:ARR,a:DARR,n:SI,m:SI,N:SI): (SI,SI) == {
		--TRACE("pivot1:, n = ", n); TRACE("m = ", m); TRACE("N = ", N);
		i:SI := 1;
		while i<=n+m-1 repeat {
			while i<=n+m-1 and b(i)~=0 repeat i := i+1;
			i=n+m => return (0, 0);
			j:SI := 1;
			while j<=N and a(i)(j)=0 repeat j := j+1;
			if j=N+1 then b(i) := -1 else return (i,j);
		};
		(0,0)
	}

	local pivot2(b:ARR,a:DARR,n:SI,m:SI,N:SI): (SI,SI) == {
		--TRACE("pivot2:, n = ", n); TRACE("m = ", m); TRACE("N = ", N);
		i:SI := 1;
		while i<=n+m-1 and a(i)(N+1)>=0 repeat i := i+1;
		i=n+m => return (0, 0);
		imin := i;  
		while i<n+m-1 repeat {
			i := i+1;
			while i<=n+m-1 and a(i)(N+1)>=0 repeat i := i+1;
			if i<=n+m-1 and b(i)<b(imin) then
				imin := i;
		};
		j:SI := 1;
		while j<=N and a(imin)(j)>=0 repeat j := j+1;
		(imin,j)
	}

	local pivot3(a:DARR,n:SI,m:SI,N:SI): (SI,SI) == {
		j:SI := 1;
		while j<=N and a(n+m)(j)<=0 repeat j := j+1;
		if j=N+1 then return (0,0);
		i:SI := 1;
		while i<=n+m-1 and a(i)(j)<=0 repeat i := i+1;
		ASSERT(a(i)(j) = 1);
		imin := i;
		while i<n+m-1 repeat {
			i := i+1;
			while i<=n+m-1 and a(i)(j)<=0 repeat i := i+1;
			if i<=n+m-1 then {
				ASSERT(a(imin)(j) = 1);
				k:SI := N+1;
				while k<N+n+m and a(i)(k)=a(imin)(k) repeat k := k+1;
				if a(i)(k)<a(imin)(k) then
					imin := i;
			}
		};
		(imin,j);
	}

	local applyPivot!(a:DARR,i0:SI,j0:SI,n:SI,m:SI): () == {
		if a(i0)(j0)=1 then {
			for ii in 1..n repeat
				if ii~=i0 then {
					f := a(ii)(j0);
					if f~=0 then
						if f=1 then
							for j in 1..m repeat
								a(ii)(j) := a(ii)(j)-a(i0)(j);
						else
							if f=-1 then
								for j in 1..m repeat
									a(ii)(j) := a(ii)(j)+a(i0)(j);
							else {
								c := a(ii)(j0);
								for j in 1..m repeat
									a(ii)(j) := a(ii)(j)-c*a(i0)(j);
							}
				}
		}
		else {
			for ii in 1..n repeat
				if ii~=i0 then {
					f := a(ii)(j0);
					if f~=0 then
						if f=1 then
							for j in 1..m repeat
								a(ii)(j) := a(ii)(j)+a(i0)(j);
						else
							if f=-1 then
								for j in 1..m repeat
									a(ii)(j) := a(ii)(j)-a(i0)(j);
							else {
								c := a(ii)(j0);
								for j in 1..m repeat
									a(ii)(j) := a(ii)(j)+c*a(i0)(j);
							}
				};
			for j in 1..m repeat
				a(i0)(j) := -a(i0)(j);
		}
	}
}

