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
------------------------   sit_linalg.as   -----------------------
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	B == Boolean;
	I == MachineInteger;
	V == Vector;
	A == Array;
	ARR == PrimitiveArray;
}

#if ALDOC
\thistype{LinearAlgebra}
\History{Manuel Bronstein}{25/11/99}{created}
\Usage{import from \this(R, M)}
\Params{
{\em R} & \astype{CommutativeRing} & The coefficient domain\\
{\em M} & \astype{MatrixCategory} R & A matrix type\\
}
\Descr{\this(R, M) provides basic linear algebra functionalities
for matrices over $R$.}
\begin{exports}
\asexp{determinant}: & M $\to$ R & Determinant\\
\asexp{factorOfDeterminant}:
& M $\to$ (\astype{Boolean}, R) & Probable determinant\\
\asexp{invertibleSubmatrix}:
& M $\to$ (\astype{Boolean}, AZ, AZ) & Probable maximal minor\\
\asexp{maxInvertibleSubmatrix}: & M $\to$ (AZ, AZ) & Maximal minor\\
\asexp{rank}: & M $\to$ \astype{MachineInteger} & Rank\\
\asexp{rankLowerBound}:
& M $\to$ (\astype{Boolean}, \astype{MachineInteger}) & Probable rank\\
\asexp{span}: & M $\to$ AZ & Span\\
\end{exports}
\begin{exports}[if R has \astype{IntegralDomain} then]
\asexp{cycle}: & (V $\to$ V, V) $\to$ (V, M) &  First dependence relation\\
\asexp{cycle}: & (M, V) $\to$ (V, M) & First dependence relation\\
\asexp{firstDependence}:
& (\astype{Generator} V, \astype{MachineInteger}) $\to$ V &
First dependence relation\\
\asexp{inverse}: & M $\to$ (M, V) & Inverse\\
\asexp{kernel}: & M $\to$ M & Kernel\\
\asexp{particularSolution}: & (M, M) $\to$ (M, V) & A solution\\
\asexp{solve}: & (M, M) $\to$ (M, M, V) & All solutions\\
\asexp{subKernel}: & M $\to$ (\astype{Boolean}, M) & Subspace of the kernel\\
\end{exports}
\begin{aswhere}
AZ &==& \astype{Array} \astype{MachineInteger}\\
V &==& \astype{Vector} R\\
\end{aswhere}
#endif

LinearAlgebra(R:CommutativeRing, M:MatrixCategory R): with {
	if R has IntegralDomain then {
		cycle: (M, V R) -> (V R, M);
		cycle: (V R -> V R, V R) -> (V R, M);
#if ALDOC
\aspage{cycle}
\Usage{\name(f,v)\\ \name(A,v)}
\Signatures{
\name: & (\astype{Vector} R $\to$ \astype{Vector} R, \astype{Vector} R)
$\to$ (\astype{Vector} R, M)\\
\name: & (M, \astype{Vector} R) $\to$ (\astype{Vector} R, M)\\
}
\Params{
{\em f} & \astype{Vector} R $\to$ \astype{Vector} R & A map\\
{\em A} & M & A matrix\\
{\em v} & \astype{Vector} R & A vector whose cycle is wanted\\
}
\Retval{
Returns $([a_0,\dots,a_n], m)$ where
$$
\sum_{i=0}^n a_i A^i v = 0
\quad\paren{\mbox{resp.~} \sum_{i=0}^n a_i f^i(v) = 0}\,,
$$
and the columns of $m$ are $v,f(v),\dots,f^n(v)$
(resp.~$v,Av,\dots,A^n v$).
}
\Remarks{
The relation is as small as possible, meaning that
$v,f(v),\dots,f^{n-1}(v)$
(resp.~$v,Av,\dots,A^{n-1} v$)
are linearly independent over R.
The iterates of $v$ under $f$ must all have the same dimension.
}
\seealso{\asexp{firstDependence}}
#endif
	}
	determinant: M -> R;
#if ALDOC
\aspage{determinant}
\Usage{\name~a}
\Signature{M}{R}
\Params{ {\em a} & M & A matrix\\ }
\Retval{ Returns the determinant of {\em a}.}
\seealso{\asexp{factorOfDeterminant}}
#endif
	factorOfDeterminant: M -> (B, R);
#if ALDOC
\aspage{factorOfDeterminant}
\Usage{\name~a}
\Signature{M}{(\astype{Boolean}, R)}
\Params{ {\em a} & M & A matrix\\ }
\Retval{ Returns $(det?, d)$ such that $d$ is always a factor of
the determinant of {\em a}, and $d$ is exactly the determinant of $a$
if $det?$ is \true. }
\Remarks{$d$ can also happen to be the determinant of $a$ when $det?$ is
\false, but the algorithm was unable to prove it.}
\seealso{\asexp{determinant}}
#endif
	if R has IntegralDomain then {
		firstDependence: (Generator V R, I) -> V R;
#if ALDOC
\aspage{firstDependence}
\Usage{\name(gen,n)}
\Signature{(\astype{Generator} \astype{Vector} R, \astype{MachineInteger})}
{\astype{Vector} R}
\Params{
{\em gen} & \astype{Generator} \astype{Vector} R & A generator of vectors\\
{\em n} & \astype{MachineInteger} & The dimension of the vectors generated\\
}
\Descr{
Returns a vector {\em v} which contains the coefficients
of a dependence relation among the vectors generated by {\em gen}. The
relation is as small as possible, meaning that if {\em v} has
dimension {\em m} then the first $m-1$ vectors generated are
linearly independent over R.
The dimension of the vectors generated by {\em gen} must be
{\em n}. There must be a relation between the vectors generated.
}
\seealso{\asexp{cycle}}
#endif
		inverse: M -> (M, V R);
#if ALDOC
\aspage{inverse}
\Usage{\name~a}
\Signature{M}{(M, \astype{Vector} R)}
\Params{ {\em a} & M & A matrix\\ }
\Retval{ Returns $(b, [d_1,\dots,d_n])$ such that
$$
a b = \pmatrix{
d_1 &     &        & \cr
    & d_2 &        & \cr
    &     & \ddots & \cr
    &     &        & d_n \cr
}\,.
$$
}
\Remarks{$\prod_{i=1}^n d_i \ne 0$ if and only if $a$ is invertible.
In that case, $a^{-1} = b d^{-1}$ where $d$ is the diagonal matrix
with diagonal $d_1,\dots,d_n$. To compute the inverse of $a$ as
a product of a diagonal matrix on the left rather than the right,
let $(b,d)$ be the result of calling
\name{} on \asfunc{MatrixCategory}{transpose}($a$).
Then, $(a^t)^{-1} = b d^{-1}$, so $a^{-1} = d^{-1} b^t$.
When $R$ is a \astype{Field}, then $d_i \in \{0,1\}$ for $1 \le i \le n$,
so $b = a^{-1}$ when $R$ is a \astype{Field} and $a$ is invertible.}
#endif
	}
	invertibleSubmatrix: M -> (B, A I, A I);	-- rows/cols
#if ALDOC
\aspage{invertibleSubmatrix}
\Usage{\name~a}
\Signature{M}{(\astype{Boolean}, \astype{Array} \astype{MachineInteger},
\astype{Array} \astype{MachineInteger})}
\Params{ {\em a} & M & A matrix\\ }
\Retval{ Returns $(max?, [r_1,\dots,r_r], [c_1,\dots,c_r])$
where $r \le \mbox{rank}(a)$
and the submatrix of $a$ formed by the intersections of the rows $r_i$
and $c_i$ is always invertible. If $max?$ is \true, then $r$ is exactly
the rank of $a$ and the given minor is of maximal size.}
\Remarks{$r$ can also happen to be the rank of $a$ when $max?$ is \false,
but the algorithm was unable to prove it.}
\seealso{\asexp{maxInvertibleSubmatrix}}
#endif
	if R has IntegralDomain then {
		kernel: M -> M;
#if ALDOC
\aspage{kernel}
\Usage{\name~a}
\Signature{M}{M}
\Params{ {\em a} & M & A matrix\\ }
\Retval{ Returns a matrix whose columns form a basis of the kernel of {\em a}.}
\seealso{\asexp{solve},\asexp{subKernel}}
#endif
	}
	maxInvertibleSubmatrix: M -> (A I, A I);	-- rows/cols
#if ALDOC
\aspage{maxInvertibleSubmatrix}
\Usage{\name~a}
\Signature{M}{(\astype{Array} \astype{MachineInteger},
\astype{Array} \astype{MachineInteger})}
\Params{ {\em a} & M & A matrix\\ }
\Retval{ Returns $([r_1,\dots,r_r], [c_1,\dots,c_r])$
where $r$ is the rank of {\em a}
and the submatrix of $a$ formed by the intersections of the rows $r_i$
and $c_i$ is invertible.}
\seealso{\asexp{invertibleSubmatrix}}
#endif
	if R has IntegralDomain then {
		particularSolution: (M, M) -> (M, V R);
#if ALDOC
\aspage{particularSolution}
\Usage{\name(a, b)}
\Signature{(M, M)}{(M, \astype{Vector} R)}
\Params{ {\em a, b} & M & Matrices\\ }
\Retval{ Returns $(m, [d_1,\dots,d_n])$ such that
$$
a m = b \pmatrix{
d_1 &     &        & \cr
    & d_2 &        & \cr
    &     & \ddots & \cr
    &     &        & d_n \cr
}\,.
$$
}
\Remarks{For each $i$, $d_i \ne 0$ if and only if the system
$a x = \sth{i}$ column of $b$ has a solution, which is then $d_i^{-1}$
times the $\sth{i}$ column of $m$.
When $R$ is a \astype{Field}, then $d_i \in \{0,1\}$ for $1 \le i \le n$,
so $m$ is a solution of $a x = b$ when $R$ is a \astype{Field} and all
the $d_i$'s are nonzero.}
\seealso{\asexp{solve}}
#endif
	}
	rank: M -> I;
#if ALDOC
\aspage{rank}
\Usage{\name~a}
\Signature{M}{\astype{MachineInteger}}
\Params{ {\em a} & M & A matrix\\ }
\Retval{ Returns the rank of {\em a}.  }
\seealso{\asexp{rankLowerBound},\asexp{span}}
#endif
	rankLowerBound: M -> (B, I);
#if ALDOC
\aspage{rankLowerBound}
\Usage{\name~a}
\Signature{M}{(\astype{Boolean}, \astype{MachineInteger})}
\Params{ {\em a} & M & A matrix\\ }
\Retval{ Returns $(rank?, r)$ such that $r \le \mbox{rank}(a)$,
and $r$ is exactly the rank of $a$ if $rank?$ is \true. }
\Remarks{$r$ can also happen to be the rank of $a$ when $rank?$ is \false,
but the algorithm was unable to prove it.}
\seealso{\asexp{rank},\asexp{span}}
#endif
	span: M -> A I;
#if ALDOC
\aspage{span}
\Usage{\name~a}
\Signature{M}{\astype{Array} \astype{MachineInteger}}
\Params{ {\em a} & M & A matrix\\ }
\Retval{ Returns $[c_1,\dots,c_r]$ where $r$ is the rank of {\em a}
and the span of $a$ is generated by its columns $c_1,\dots,c_r$.}
\seealso{\asexp{rank}}
#endif
	if R has IntegralDomain then {
		solve: (M, M) -> (M, M, V R);
#if ALDOC
\aspage{solve}
\Usage{\name(a, b)}
\Signature{(M, M)}{(M, M, \astype{Vector} R)}
\Params{ {\em a, b} & M & Matrices\\ }
\Retval{ Returns $(w, m, [d_1,\dots,d_n])$ such that the columns
of $w$ form a basis of the kernel of $a$ and
$$
a m = b \pmatrix{
d_1 &     &        & \cr
    & d_2 &        & \cr
    &     & \ddots & \cr
    &     &        & d_n \cr
}\,.
$$
}
\Remarks{For each $i$, $d_i \ne 0$ if and only if the system
$a x = \sth{i}$ column of $b$ has a solution, which is then $d_i^{-1}$
times the $\sth{i}$ column of $m$.
When $R$ is a \astype{Field}, then $d_i \in \{0,1\}$ for $1 \le i \le n$,
so the general solution of $a x = b$ when $R$ is a \astype{Field} and all
the $d_i$'s are nonzero is $x = m + \sum_j r_j w_j$ where $w_j$ is the
$\sth{j}$ column of $w$.}
\seealso{\asexp{kernel},\asexp{particularSolution}}
#endif
		subKernel: M -> (B, M);
#if ALDOC
\aspage{subKernel}
\Usage{\name~a}
\Signature{M}{(\astype{Boolean}, M)}
\Params{ {\em a} & M & A matrix\\ }
\Retval{ Returns $(ker?, m)$ such that the columns of $m$, which are always
linearly independent over R, generate a subspace of the kernel of $a$,
and generate the full kernel if $ker?$ is \true.}
\Remarks{$m$ can also happen to generate the full kernel of $a$ when $ker?$ is
\false, but the algorithm was unable to prove it.}
\seealso{\asexp{kernel}}
#endif
	}
} == add {
	local gcd?:Boolean	== R has GcdDomain;
	local laring?:Boolean	== R has LinearAlgebraRing;
	local special?:Boolean	== R has Specializable;

	local elim:LinearEliminationCategory(R, M) == {
		R has Field => OrdinaryGaussElimination(R pretend Field, M);
		R has IntegralDomain =>
			TwoStepFractionFreeGaussElimination(_
					R pretend IntegralDomain, M);
		DivisionFreeGaussElimination(R, M);
	}

	determinant(m:M):R == {
		laring? => ladet m;
		determinant(m)$elim;
	}

	rank(m:M):I == {
		laring? => larank m;
		rank(m)$elim;
	}

	span(m:M):A I == {
		laring? => laspan m;
		span(m)$elim;
	}

	maxInvertibleSubmatrix(m:M):(A I,A I) == {
		laring? => lamaxinv m;
		maxInvertibleSubmatrix(m)$elim;
	}

	factorOfDeterminant(m:M):(B, R) == {
		laring? => lafactdet m;
		(true, determinant m);
	}

	rankLowerBound(m:M):(B, I) == {
		import from Partial Cross(B, I);
		laring? => lalbrank m;
		special? => {
			failed?(u := speclbrank m) => (true, rank m);
			retract u;
		}
		(true, rank m);
	}

	invertibleSubmatrix(m:M):(B, A I, A I) == {
		laring? => lasubinv m;
		(r, c) := maxInvertibleSubmatrix m;
		(true, r, c);
	}

	if R has IntegralDomain then {
		macro RID == R pretend IntegralDomain;

		cycle(a:M, v:V R):(V R, M) == cycle((w:V R):V R +-> a * w, v);

		subKernel(m:M):(B, M) == {
			laring? => lasubker m;
			(true, kernel m);
		}

		inverse(m:M):(M, V R) == {
			laring? => lainv m;
			inverse! copy m;
		}

		solve(a:M, b:M):(M, M, V R) == {
			import from I;
			(ra, ca) := dimensions a;
			(rb, cb) := dimensions b;
			assert(ra = rb);
			if zero? ra then { a := zero(1, ca); b := zero(1, cb) }
			laring? => lasolve(a, b);
			solve!(copy a, copy b);
		}

		particularSolution(a:M, b:M):(M, V R) == {
			laring? => lapsol(a, b);
			psol!(copy a, copy b);
		}

		kernel(m:M):M == {
			import from I, OverdeterminedLinearSystemSolver(RID, M);
			(r, c) := dimensions m;
			zero? c => zero(0, 0);
			if zero? r then m := zero(1, c);
			laring? => kernel!(m, lakernel);
			kernel!(copy m, nullspace!);
		}

		cycle(f:V R -> V R, v:V R):(V R, M) == {
			import from I;
			n := #v;
			m := zero(n, next n);
			dep := firstDependence(cycle(f, v, m), #v);
			(dep, m);
		}

		-- stores each vector generated as a column of m
		local cycle(f:V R -> V R, v:V R, m:M):Generator V R == {
			generate {
				j:I := 1;
				n := numberOfRows m;
				vv := copy v;
				for i in 1..n repeat m(i,j) := vv.i;
				yield vv;
				repeat {
					vv := f vv;
					j := next j;
					for i in 1..n repeat m(i,j) := vv.i;
					yield vv;
				}
			}
		}

		local first(w:V R, n:I):V R == {
			assert(n <= #w);
			n = #w => w;
			v := zero n;
			for i in 1..n repeat v.i := w.i;
			v;
		}

		firstDependence(gen:Generator V R, n:I):V R == {
			import from ARR I;
			laring? => ladep(gen, n);
			(a,p,r,d) := dependence(gen, n)$elim;
			st:ARR I:= new r;	-- ignore st(0)
			for i in 1..prev r repeat st(i) := i;
			gcd? => first(gcddep(a,p,st,prev r,r), r);
			first(generaldep(a,p,st,prev r,r,d), r);
		}

		local solve!(a:M, b:M):(M, M, V R) == {
			import from List V R;
			(psol, den, k) := {
				gcd? => solvegcddomain!(a, b);
				solvegeneral!(a, b);
			}
			([v for v in k], psol, den);
		}

		local psol!(a:M, b:M):(M, V R) == {
			gcd? => psolgcddomain!(a, b);
			psolgeneral!(a, b);
		}

		local inverse!(a:M):(M, V R) == {
			assert(square? a);
			gcd? => invgcddomain! a;
			invgeneral! a;
		}

		local nullspace!(a:M):M == {
			import from List V R;
			-- TEMPORARY: BLOODY 1.1.12p4 COMPILER BUG OTHERWISE
			-- (p,r,st,d) := rowEchelon!(a)$elim;
			(p,r,st,d) :=
				rowEchelon!(a, zero(numberOfRows a, 0$I))$elim;
			k := {
				gcd? => nullgcddomain!(a, p, r, st);
				nullgeneral!(a, p, r, st);
			}
			[v for v in k];
		}

		local generaldep(a:M, p:I->I, st:ARR I, c:I, r:I, d:R):V R == {
			import from Backsolve(RID, M);
			backsolve(a,p,st,c,r,d);
		}

		local invgeneral!(a:M):(M, V R) == {
			import from Backsolve(RID, M);
			(p,r,st,d,w) := extendedRowEchelon!(a)$elim;
			det := deter(a,p,r,d)$elim;
			backsolve(a,p,st,r,w,det);
		}

		local nullgeneral!(a:M, p:I->I, r:I, st:ARR I):List V R == {
			import from ARR R, Backsolve(RID, M);
			den := denominators(a,p,r,st)$elim;
			k:List V R := empty;
			(n, m) := dimensions a;
			un:R := 1;
			for j in 1..st(1)-1 repeat
				k := cons(backsolve(a,p,st,0,j,un),k);
			for i in 1..prev r repeat
				for j in next(st i)..prev st(next i) repeat
					k:=cons(backsolve(a,p,st,i,j,den(i)),k);
			if r > 0 then
				for j in next(st r)..m repeat
					k:=cons(backsolve(a,p,st,r,j,den(r)),k);
			k;
		}

		local solvegeneral!(a:M, b:M):(M, V R, List V R) == {
			import from Backsolve(RID, M);
			(p,r,st,d) := rowEchelon!(a, b)$elim;
			det := deter(a,p,r,d)$elim;
			(psol, den) := backsolve(a,p,st,r,b,det);
			(psol, den, nullgeneral!(a, p, r, st));
		}

		local psolgeneral!(a:M, b:M):(M, V R) == {
			import from Backsolve(RID, M);
			(p,r,st,d) := rowEchelon!(a, b)$elim;
			det := deter(a,p,r,d)$elim;
			backsolve(a,p,st,r,b,det);
		}
	}

	if R has GcdDomain then {
		macro RGD == R pretend GcdDomain;

		local gcddep(a:M, p:I->I, st:ARR I, c:I, r:I):V R == {
			import from Backsolve(RGD, M);
			backsolve(a,p,st,c,r);
		}

		local invgcddomain!(a:M):(M, V R) == {
			import from Backsolve(RGD, M);
			(p,r,st,d,w) := extendedRowEchelon!(a)$elim;
			backsolve(a,p,st,r,w);
		}

		local nullgcddomain!(a:M, p:I->I, r:I, st:ARR I):List V R == {
			import from Backsolve(RGD, M);
			k:List V R := empty;
			(n, m) := dimensions a;
			for j in 1..prev(st 1) repeat
				k := cons(backsolve(a,p,st,0,j),k);
			for i in 1..prev r repeat
				for j in next(st i)..prev st(next i) repeat
					k:=cons(backsolve(a,p,st,i,j),k);
			if r > 0 then for j in next(st r)..m repeat
					k:=cons(backsolve(a,p,st,r,j),k);
			k;
		}

		local solvegcddomain!(a:M, b:M):(M, V R, List V R) == {
			import from Backsolve(RGD, M);
			(p,r,st,d) := rowEchelon!(a, b)$elim;
			(psol, den) := backsolve(a,p,st,r,b);
			(psol, den, nullgcddomain!(a, p, r, st));
		}

		local psolgcddomain!(a:M, b:M):(M, V R) == {
			import from Backsolve(RGD, M);
			(p,r,st,d) := rowEchelon!(a, b)$elim;
			backsolve(a,p,st,r,b);
		}
	}

	if R has Specializable then {
		macro RSPEC == R pretend Join(CommutativeRing, Specializable);

		speclbrank(m:M):Partial Cross(B, I) ==
			rankLowerBound(m)$SpecializationLinearAlgebra(RSPEC, M);
	}

	if R has LinearAlgebraRing then {
		local ladet(a:M):R == {
			import from R;
			determinant(M)(a);
		}

		local larank(a:M):I == {
			import from R;
			rank(M)(a);
		}

		local laspan(a:M):A I == {
			import from R;
			span(M)(a);
		}

		local lamaxinv(a:M):(A I, A I) == {
			import from R;
			maxInvertibleSubmatrix(M)(a);
		}

		local lafactdet(a:M):(B, R) == {
			import from R;
			factorOfDeterminant(M)(a);
		}

		local lalbrank(a:M):(B, I) == {
			import from R;
			rankLowerBound(M)(a);
		}

		local lasubinv(a:M):(B, A I, A I) == {
			import from R;
			invertibleSubmatrix(M)(a);
		}

		local lasubker(a:M):(B, M) == {
			import from R;
			subKernel(M)(a);
		}

		local lainv(a:M):(M, V R) == {
			import from R;
			inverse(M)(a);
		}

		local lasolve(a:M, b:M):(M, M, V R) == {
			import from R;
			solve(M)(a, b);
		}

		local lapsol(a:M, b:M):(M, V R) == {
			import from R;
			particularSolution(M)(a, b);
		}

		local lakernel(a:M):M == {
			import from R;
			kernel(M)(a);
		}

		local ladep(gen:Generator V R, n:I):V R == {
			import from R;
			linearDependence(gen, n);
		}
	}
}
