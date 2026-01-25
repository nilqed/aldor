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
------------------------------ sit_optspow.as --------------------------------
-- Copyright (c) Thom Mulders 1996
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1996
-----------------------------------------------------------------------------

#include "sumit"

macro {
	SI == MachineInteger;
	Z == Integer;
	PA == PrimitiveArray;
}

#if ALDOC
\thistype{OptimizeSymmetricPower}
\History{Thom Mulders}{23 September 96}{created}
\Usage{import from \this(R,M)}
\Params{
{\em R} & \astype{Ring} & A coefficient ring\\
{\em M} & \astype{MatrixCategory} R & A matrix type over R\\
}
\Descr{\name(R, M) provides the optimization mechanism used for
speeding up symmetric power computations.}
\begin{exports}
\asexp{optimize}:
& (M, R $\to$ \astype{Partial} Z) $\to$
(\astype{PrimitiveArray} Z, \astype{PrimitiveArray} Z, Z) & \\
\end{exports}
\begin{aswhere}
Z &==& \astype{MachineInteger}\\
\end{aswhere}
#endif

OptimizeSymmetricPower(R:Ring, M:MatrixCategory R): with {
	optimize: (M,R->Partial SI) -> (PA Z,PA Z,SI);
#if ALDOC
\aspage{optimize}
\Usage{\name(a,f)}
\Signature{(M, R $\to$ \astype{Partial} Z)}
{(\astype{PrimitiveArray} Z, \astype{PrimitiveArray} Z, Z)}
\begin{aswhere}
Z &==& \astype{MachineInteger}\\
\end{aswhere}
\Params{
{\em a} & M & A matrix\\
{\em f} & R $\to$ \astype{Partial} \astype{MachineInteger}& A partial function\\
}
\Descr{
This provides the optimization described in:\\
M.~Bronstein, T.~Mulders \& J.A.~Weil,
{\em On symmetric powers of differential operators},
Proceedings of ISSAC'97, ACM Press (1997), 156--163.
}
#endif
} == add {
	optimize(a:M,f:R->Partial SI): (PA Z,PA Z,SI) == {
		(n, m) := dimensions a;
		linprog(applyFunction(a, f), n, m);
	}

	-- Map f to a. If the value of f applied to an entry of a is 'failed'
	-- the corresponding value will be -1.
	local applyFunction(a:M, f:R->Partial SI): PA PA SI == {
		import from PA SI, Partial SI, SI;
		TIMESTART;
		(n, m) := dimensions a;
		mat:PA PA SI := new n;
		for i in 0..prev n repeat {
			mat.i := new m;
			for j in 0..prev m repeat {
				v := f a(next i, next j);
				mat.i.j := { failed? v => -1; retract v }
			}
		}
		TIME("optimize::time to create order matrix = ");
		mat;
	}

#if TRACE
	local trace(a:PA PA SI, n:SI, m:SI):() == {
		import from TextWriter, String, Character, PA SI;
		for i in 0..prev n repeat {
			for j in 0..prev m repeat stderr << a.i.j << " ";
			stderr << newline;
		}
	}

	local trace(a:PA SI, n:SI):() == {
		import from TextWriter, String, Character;
		for i in 0..prev n repeat stderr << a.i << " ";
		stderr << newline;
	}

	local trace(a:PA Z, n:SI):() == {
		import from TextWriter, String, Character, Z;
		for i in 0..prev n repeat stderr << a.i << " ";
		stderr << newline;
	}
#endif

-- a represents a matrix with SI coefficients. Vectors r and c with Integer
-- coefficients are computed such that
-- 1) r(i)+c(j)+a(i)(j)>=0 for all i,j
-- 2) sum(r(i)+c(j)+a(i)(j); i,j such that a(i)(j)>=0) is minimal
-- Also this minimal sum is returned.
-- In fact the dual linear programming problem is solved.
-- By simulating the process of elimination on an identity matrix
-- the actual solution is also found.
-- 
--  DESCRIPTION OF ALGORITHM
--  
--
-- The tableau of the dual problem has the following shape:
--
--  [ A  b I ]
--  [ -c

	local linprog(a:PA PA SI,n:SI,m:SI): (PA Z,PA Z,SI) == {
		import from PA SI, Z, PA Z;
		TRACE("optimize::linprog, n = ", n);
		TRACE("optimize::linprog, m = ", m);
#if TRACE
		trace(a, n, m);
#endif
		TIMESTART;
		R:PA SI := new(n,0);
		C:PA SI := new(m,0);
		N:SI := 0;
		sum:SI := 0;
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 0..prev n repeat for j in 0..prev m repeat {
		i:SI := 0; while i < n repeat {
			j:SI := 0;
			while j < m repeat {
				if a.i.j >= 0 then {
					sum := sum+a.i.j;
					N := next N;
					R.i := next(R.i);
					C.j := next(C.j);
				}
				j := next j;
			}
			i := next i;
		}
		TRACE("optimize::linprog, N = ", N);
		mat:PA PA SI := new (n+m);
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 0..prev(n+m) repeat mat.i := new(N+n+m, 0);
		i := 0;
		while i < n+m repeat { mat.i := new(N+n+m, 0); i := next i }
		TRACE("optimize::linprog, all mat(i) allocated", "");
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 0..n+m-2 repeat mat(i)(N+1+i) := 1;
		i := 0;
		while i < prev(n+m) repeat { mat(i)(N+1+i) := 1; i := next i }
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 1..prev n repeat mat(prev i)(N) := R.i;
		i := 1;
		while i < n repeat { mat(prev i)(N) := R.i; i := next i }
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for j in 0..prev m repeat mat(n-1+j)(N) := C.j;
		j:SI := 0;
		while j < m repeat { mat(n-1+j)(N) := C.j; j := next j }
		ind:SI := 0;
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for j in 0..prev m repeat {
		j:SI := 0; while j < m repeat {
			if a.0.j >=0 then {
				mat(n-1+j)(ind) := 1;
				ind := next ind;
			}
			j := next j;
		}
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 1..prev n repeat for j in 0..prev m repeat {
		i := 1; while i < n repeat {
			j := 0; while j < m repeat {
				if a.i.j >= 0 then {
					mat(i-1)(ind) := 1;
					mat(n-1+j)(ind) := 1;
					ind := next ind;
				}
				j := next j;
			}
			i := next i;
		}
		base:PA SI := new(n+m-1,-2);
		(i0,j0) := pivot1(base,mat,n,m,N);
		while i0 >= 0 repeat {
			base.i0 := j0;
			applyPivot!(mat,i0,j0,n+m-1,N+n+m);
			(i0,j0) := pivot1(base,mat,n,m,N);
		}
		(i0,j0) := pivot2(base,mat,n,m,N);
		while i0 >= 0 repeat {
			base.i0 := j0;
			applyPivot!(mat,i0,j0,n+m-1,N+n+m);
			(i0,j0) := pivot2(base,mat,n,m,N);
		}
		ind := 0;
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 0..prev n repeat for j in 0..prev m repeat {
		i := 0; while i < n repeat {
			j := 0; while j < m repeat {
				if a.i.j >= 0 then {
					mat(n+m-1)(ind) := -a.i.j;
					ind := next ind;
				}
				j := next j;
			}
			i := next i;
		}
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 0..n+m-2 repeat {
		i := 0; while i < prev(n+m) repeat {
			if base.i >= 0 then {
				c := mat(n+m-1)(base.i);
				-- TEMPORARY: LOOP-INLINING BUG 1203
				-- for j in 0..N+n+m-1 repeat {
				j := 0; while j < N+n+m repeat {
					mat(n+m-1)(j):= mat(n+m-1)(j)-c*mat.i.j;
					j := next j;
				}
			}
			i := next i;
		}
		(i0,j0) := pivot3(mat,n,m,N);
		while i0 >= 0 repeat {
			applyPivot!(mat,i0,j0,n+m,N+n+m);
			(i0,j0) := pivot3(mat,n,m,N);
		}
		row:PA Z := new n;
		col:PA Z := new m;
		row.0 := 0;
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 1..prev n repeat row.i := (-mat(n+m-1)(N+i))::Z;
		i := 1; while i < n repeat {
			row.i := (-mat(n+m-1)(N+i))::Z;
			i := next i;
		}
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for j in 0..prev m repeat col.j := (-mat(n+m-1)(N+n+j))::Z;
		j := 0; while j < m repeat {
			 col.j := (-mat(n+m-1)(N+n+j))::Z;
			j := next j;
		}
#if TRACE
		trace(row, n);
		trace(col, m);
#endif
		mincol:= col.0;
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for j in 1..prev m repeat {
		j := 1; while j < m repeat {
			if col.j < mincol then mincol := col.j;
			j := next j;
		}
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for j in 0..prev m repeat col.j := col.j - mincol;
		j := 0; while j < m repeat { col.j := col.j-mincol; j:=next j }
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 0..prev n repeat row.i := row.i + mincol;
		i := 0; while i < n repeat { row.i := row.i+mincol; i:=next i }
		TIME("optimize::time for linear programming = ");
#if TRACE
		trace(row, n);
		trace(col, m);
#endif
		(row,col,sum-mat(n+m-1)(N));
	}

	local pivot1(b:PA SI,a:PA PA SI,n:SI,m:SI,N:SI): (SI,SI) == {
		TRACE("pivot1:, n = ", n); TRACE("m = ", m); TRACE("N = ", N);
		i:SI := 0;
		while i < n+m-1 repeat {
			while i< n+m-1 and b.i >= -1 repeat i := next i;
			i=n+m-1 => return (-1, -1);
			j:SI := 0;
			while j<N and a.i.j=0 repeat j := next j;
			if j=N then b.i := -1 else return(i,j);
		}
		(-1,-1)
	}

	local pivot2(b:PA SI,a:PA PA SI,n:SI,m:SI,N:SI): (SI,SI) == {
		TRACE("pivot2:, n = ", n); TRACE("m = ", m); TRACE("N = ", N);
		i:SI := 0;
		while i < n+m-1 and a.i.N >= 0 repeat i := next i;
		i=n+m-1 => (-1, -1);
		imin := i;  
		while i < n+m-2 repeat {
			i := next i;
			while i < n+m-1 and a.i.N >= 0 repeat i := next i;
			if i < n+m-1 and b.i < b.imin then imin := i;
		}
		j:SI := 0;
		while j < N and a.imin.j >= 0 repeat j := next j;
		(imin, j)
	}

	local pivot3(a:PA PA SI,n:SI,m:SI,N:SI): (SI,SI) == {
		import from PA SI;
		j:SI := 0;
		while j < N and a(n+m-1)(j) <= 0 repeat j := next j;
		j=N => (-1, -1);
		i:SI := 0;
		while i < n+m-1 and a.i.j <= 0 repeat i := next i;
		assert(a.i.j = 1);
		imin := i;
		while i < n+m-2 repeat {
			i := next i;
			while i < n+m-1 and a.i.j <= 0 repeat i := next i;
			if i < n+m-1 then {
				assert(a.imin.j = 1);
				k := N;
				while k < N+n+m-1 and a.i.k = a.imin.k repeat
					k := next k;
				if a.i.k < a.imin.k then imin := i;
			}
		}
		(imin, j);
	}

	local applyPivot!(a:PA PA SI,i0:SI,j0:SI,n:SI,m:SI): () == {
		import from PA SI;
		m1 := prev m;
		if a.i0.j0=1 then for ii in 0..prev n | ii ~= i0 repeat {
			f := a.ii.j0;
			if f~=0 then {
				if f=1 then for j in 0..m1 repeat
					a.ii.j := a.ii.j - a.i0.j;
				else {
					if f=-1 then for j in 0..m1 repeat
						a.ii.j := a.ii.j + a.i0.j;
					else for j in 0..m1 repeat
							a.ii.j:=a.ii.j-f*a.i0.j;
				}
			}
		}
		else {
		    assert(a.i0.j0 = -1);
		    for ii in 0..prev n repeat {
			if ii ~= i0 then {
				f := a.ii.j0;
				if f ~= 0 then {
					if f=1 then for j in 0..m1 repeat
						a.ii.j := a.ii.j + a.i0.j;
					else {
						if f=-1 then
						    for j in 0..m1 repeat
							a.ii.j := a.ii.j-a.i0.j;
						else for j in 0..m1 repeat
						  a.ii.j := a.ii.j + f * a.i0.j;
					}
				}
			}
		    }
		    for j in 0..m1 repeat a.i0.j := -a.i0.j;
		}
	}
}

