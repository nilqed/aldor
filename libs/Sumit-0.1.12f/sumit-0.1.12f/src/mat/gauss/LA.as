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
------------------------------ LA.as -------------------------------------
#include "sumit"

#if ASDOC
\thistype{LinearAlgebra}
\History{Thom Mulders}{8 July 96}{created}
\History{Manuel Bronstein}{9 June 98}{added call to OverdeterminedSystemSolver}
\Usage{import from \this(R,M,E)}
\Params{
{\em R} & IntegralDomain & A coefficient ring\\
{\em M} & MatrixCategory0 R& A matrix type over R\\
{\em E} & EliminationCategory(R,M) & A way of performing linear elimination
}
\begin{exports}
cyclicDependence: & (V$\to$V,V) $\to$ V &  First dependence relation\\
cyclicDependence: & (M,V) $\to$ V & First dependence relation\\
determinant!: & M $\to$ R & Determinant of a matrix\\
determinant: & M $\to$ R & Determinant of a matrix\\
extendedRowEchelonForm: & M $\to$ (M,M) & REF of a matrix\\
firstDependence: & (Generator V,SI) $\to$ V & First dependence relation\\
nullspace!: & M $\to$ List V & Nullspace of a matrix\\
nullspace: & M $\to$ List V & Nullspace of a matrix\\
rank!: & M $\to$ SI & Rank of a matrix\\
rank: & M $\to$ SI & Rank of a matrix\\
rowEchelonForm: & M $\to$ M & REF of a matrix\\
span: & M $\to$ (SI, PrimitiveArray SI) & Span of a matrix\\
span!: & M $\to$ (SI, PrimitiveArray SI) & Span of a matrix\\
\end{exports}
\Aswhere{
SI & == & SingleInteger\\
V & == & Vector R\\
}
#endif

macro SI == SingleInteger;
macro ARR == PrimitiveArray SI;
macro V == Vector R;
macro BS == Backsolve(R,M);

LinearAlgebra(R:IntegralDomain,M:MatrixCategory0 R,E:EliminationCategory(R,M)):
    with {
	cyclicDependence: (V->V,V) -> V;
	cyclicDependence: (M,V) -> V;
#if ASDOC
\aspage{cyclicDependence}
\Usage{\name(f,v)\\ \name(a,v)}
\Signatures{
\name: & (Vector R $\to$ Vector R, Vector R) $\to$ Vector R\\
\name: & (M, Vector R) $\to$ Vector R\\
}
\Params{
{\em f} & Vector R $\to$ Vector R & A map on vectors\\
{\em a} & M & A matrix representing a linear map\\
{\em v} & Vector R & A vector whose cyclic dependence is wanted\\
}
\Retval{
\name(f,v) (resp.~\name(a, v)) returns a vector {\em w}
which contains the coefficients of a dependence relation
among the iterates of {\em v} under the map {\em f} (resp.~{\em a}).
}
\Remarks{
The relation is as small as possible, meaning that if {\em w} has
dimension {\em m} then the first $m-1$ iterates of {\em v} are
independent. The iterates of {\em v} under {\em f} must all have the
same dimension as {\em v}.
}
#endif
        determinant: M -> R;
        determinant!: M -> R;
#if ASDOC
\aspage{determinant}
\Usage{\name~a\\ \name!~a}
\Signature{M}{R}
\Params{ {\em a} & M & A matrix whose determinant has to be computed\\ }
\Retval{ Returns the determinant of {\em a}.  }
\Remarks{ If \name! is used, then the matrix {\em a} itself may be
destroyed after this operation.}
#endif
	extendedRowEchelonForm: M -> (M,M);
#if ASDOC
\aspage{extendedRowEchelonForm}
\Usage{\name~a}
\Signature{M}{(M,M)} 
\Params{
{\em a} & M & A matrix whose REF has to be computed}
\Descr{
We say that a matrix $a$ is in REF if there are $r$ (the rank) and
$j_1<j_2<\cdots<j_r$ (the stairs) such that $a(i,j_i)\neq 0$,
$a(i,j)=0$ for $j<j_i$ and $a(i,j)=0$ for $i>r$.

We say that a matrix $b$ is a REF of the matrix $a$ if $b$ is in REF
and there exists a non-singular matrix $u$ such that $ua=b$.
}
\Retval{Returns a REF {\em b} of {\em a} and the transformation matrix
{\em u} such that $ua=b$.}
#endif
	firstDependence: (Generator V,SI) -> V;
#if ASDOC
\aspage{firstDependence}
\Usage{\name(gen,n)}
\Signature{(Generator Vector R, SingleInteger)}{Vector R}
\Params{
{\em gen} & Generator Vector R & A generator of vectors\\
{\em n} & SingleInteger & The dimension of the vectors generated\\
}
\Descr{
\name(gen,n) returns a vector {\em v} which contains the coefficients
of a dependence relation among the vectors generated by {\em gen}. The
relation is as small as possible, meaning that if {\em v} has
dimension {\em m} then the first $m-1$ vectors generated are
independent. The dimension of the vectors generated by {\em gen} must be
{\em n}. There must be a relation between the vectors generated.
}
#endif
	if R has Field then {
		inverse: M -> M;
	}
	nullspace: M -> List V;
	nullspace!: M -> List V;
#if ASDOC
\aspage{nullspace}
\Usage{\name~a\\ \name!~a}
\Signature{M}{List V}
\Params{ {\em a} & M & A matrix whose nullspace has to be computed\\ }
\Retval{Returns a list of vectors which span the nullspace of {\em
a}.}
\Remarks{ If \name! is used, then the matrix {\em a} itself may be
destroyed after this operation.}
#endif
        rank: M -> SI;
	rank!: M -> SI;
#if ASDOC
\aspage{rank}
\Usage{\name~a\\ \name!~a}
\Signature{M}{SingleInteger}
\Params{ {\em a} & M & A matrix whose rank has to be computed }
\Retval{ Returns the rank of {\em a}.  }
\Remarks{ If \name! is used, then the matrix {\em a} itself may be
destroyed after this operation.}
#endif
	rowEchelonForm: M -> M;
#if ASDOC
\aspage{rowEchelonForm}
\Usage{\name~a}
\Signature{M}{M} 
\Params{ {\em a} & M & A matrix whose REF has to be computed}
\Descr{
We say that a matrix $a$ is in REF if there are $r$ (the rank) and
$j_1<j_2<\cdots<j_r$ (the stairs) such that $a(i,j_i)\neq 0$,
$a(i,j)=0$ for $j<j_i$ and $a(i,j)=0$ for $i>r$.

We say that a matrix $b$ is a REF of the matrix $a$ if $b$ is in REF
and there exists a non-singular matrix $u$ such that $ua=b$.
}
\Retval{Returns a REF of {\em a}.}
#endif
	span: M -> (SI, ARR);
	span!: M -> (SI, ARR);
#if ASDOC
\aspage{span}
\Signature{M}{(SingleInteger, PrimitiveArray SingleInteger)}
\Params{ {\em a} & M & A matrix whose span has to be computed}
\Retval{ Returns $(r, [c_1,\dots,c_r])$ where $r$ is the rank of {\em a}
and the span of $a$ is generated by its columns $c_1,\dots,c_r$.}
\Remarks{ If \name! is used, then the matrix {\em a} itself may be
destroyed after this operation.}
#endif
} == add {
	rank(a:M):SI		== rank! copy a;
	span(a:M):(SI, ARR)	== span! copy a;

	if R has Field then {
		inverse(a:M):M == {
			import from SI, E, Backsolve(R pretend GcdDomain, M);
			assert(rows a = cols a);
			(c,p,r,st,d,w) := extendedRowEchelon a;
			-- den must be a primitive array of 1's
			(sol, den) := backsolve(c,p,st,r,w);
			sol;
		}
	}

	rowEchelonForm(a:M): M == {
		import from SI,ARR,E;
		(b,p,r,st,d) := rowEchelon(a);
		n := rows b;
		m := cols b;
		c := zero(n,m);
		for i in 1..n repeat
			for j in st(i)..m repeat
				c(i,j) := b(p(i),j);
		c;
	}

	extendedRowEchelonForm(a:M): (M,M) == {
		import from SI,ARR,E;
		(b,p,r,st,d,t) := extendedRowEchelon(a);
		n := rows b;
		m := cols b;
		c := zero(n,m);
		u := zero(n,n);
		for i in 1..n repeat {
			for j in st(i)..m repeat
				c(i,j) := b(p(i),j);
			for j in 1..n repeat
				u(i,j) := t(p(i),j);
		}
		(c,u);
	}

	rank!(a:M): SI == {
		import from E;
		(p,r,st,d) := rowEchelon! a;
		r;
	}

	span!(a:M):(SI, ARR) == {
		import from E;
		(p,r,st,d) := rowEchelon! a;
		(r, st);
	}

	determinant!(a:M): R == {
		import from E;
		TRACE("LA::determinant!", "");
		(p,r,st,d) := rowEchelon!(a);
		deter(a,p,r,st,d);
	}

	determinant(a:M): R == {
		TRACE("LA::determinant: a = ", a);
		determinant!(copy a);
	}

	local gcd?:Boolean == R has GcdDomain;

	local nullgeneral!(a:M): List V == {
		import from SI,ARR,PrimitiveArray R,E,BS;
		(p,r,st,d) := rowEchelon!(a);
		den := denominators(a,p,r,st);
		k:List V := empty();
		n := rows a;
		m := cols a;
		for j in 1..st(1)-1 repeat
			k := cons(backsolve(a,p,st,j,0,1),k);
		for i in 1..r-1 repeat
			for j in st(i)+1..st(i+1)-1 repeat
				k := cons(backsolve(a,p,st,j,i,den(i)),k);
		if r > 0 then
			for j in st(r)+1..m repeat
				k := cons(backsolve(a,p,st,j,r,den(r)),k);
		k;
	}

	if R has GcdDomain then {
		local bsolve(m:M, a:ARR, b:ARR, c:SI, d:SI):V ==
			backsolve(m, a, b, c, d)$BS;

		local nullgcddomain!(a:M): List V == {
			import from SI,ARR,E,BS;
			(p,r,st,d) := rowEchelon!(a);
			k:List V := empty();
			n := rows a;
			m := cols a;
			for j in 1..st(1)-1 repeat
				k := cons(backsolve(a,p,st,j,0),k);
			for i in 1..r-1 repeat
				for j in st(i)+1..st(i+1)-1 repeat
					k := cons(backsolve(a,p,st,j,i),k);
			if r > 0 then
				for j in st(r)+1..m repeat
					k := cons(backsolve(a,p,st,j,r),k);
			k;
		}
	}

	nullspace!(a:M): List V == {
		gcd? => nullgcddomain!(a);
		nullgeneral!(a);
	}
	
	-- MB 6/98: ENSURES ANOTHER ALGO IS USED FOR OVERDETERMINED SYSTEMS,
	--          NO CHANGES FOR NON-OVERDETERMINED SYSTEMS
	-- nullspace(a:M): List V == nullspace!(copy a);
	nullspace(a:M):List V == {
		import from OverdeterminedSystemSolver(R, M);
		nullSpace!(copy a, nullspace!);
	}

	firstDependence(gen:Generator V,n:SI): V == {
		import from ARR,E,BS;
		TRACE("firstDependence: ", n);
		START__TIME;
		(a,p,r,d) := dependence(gen,n);
		TIME("firstDependence: dependence found at ");
		TRACE("dependence found of len ", r);
		st:ARR := new(r-1);
		for i in 1..r-1 repeat st(i) := i;
		v := { gcd? => bsolve(a,p,st,r,r-1); backsolve(a,p,st,r,r-1,d);}
		TIME("firstDependence: backsolving done at ");
		w := zero r;
		for i in 1..r repeat w.i := v.i;
		w;
	}

	cyclicDependence(L:V->V,v:V): V ==
		firstDependence(cycle(L,v),#v);

	cyclicDependence(a:M,v:V): V ==
		cyclicDependence((v:V):V+->a*v,v);

	local cycle(L:V->V,v:V): Generator V == generate {
		vv := copy v;
		repeat {
			yield vv;
			vv := L vv;
		}
	}
}
