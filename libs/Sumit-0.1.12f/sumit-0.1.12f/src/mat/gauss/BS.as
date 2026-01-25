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
------------------------------ BS.as --------------------------------
#include "sumit"

macro SI == SingleInteger;
macro ARR == PrimitiveArray SI;
macro V == Vector R;

#if ASDOC
\thistype{Backsolve}
\History{Thom Mulders}{8 July 96}{created}
\Usage{import from \this(R,M)}
\Params{
{\em R} & IntegralDomain & A coefficient ring\\
{\em M} & MatrixCategory0 R& A matrix type over R\\
}
\Descr{\name~(R,M) provides operations for backsolving triangular systems}
\begin{exports}
backsolve: & (M,ARR,ARR,SI,SI,R) $\to$ V & Backsolve a triangular system\\
\end{exports}
\begin{exports}[if R has GcdDomain]
backsolve: & (M,ARR,ARR,SI,SI) $\to$ V & Backsolve a triangular system\\
backsolve2: & (M,ARR,ARR,SI,SI,R) $\to$ V & Backsolve a triangular system\\
\end{exports}
\begin{aswhere}
SI &==& SingleInteger\\
ARR &==& PrimitiveArray SI\\
V &==& Vector R\\
\end{aswhere}
#endif

Backsolve(R:IntegralDomain,M:MatrixCategory0 R): with {

	backsolve: (M,ARR,ARR,SI,SI,R) -> V;
#if ASDOC
\aspage{backsolve}
\Usage{\name(a,p,st,c,r,d)}
\Signature{(M,PrimitiveArray Z,PrimitiveArray Z,Z,Z,R)}{Vector R}
\Params{
{\em a} & M & A matrix representing a Row Echelon Form (REF)\\
{\em p} & PrimitiveArray Z & A permutation of the rows of {\em a}\\
{\em st} & PrimitiveArray Z & The stairs of the REF\\
{\em c} & Z & The column to be backsolved\\
{\em r} & Z & The number of leading columns before the $c$-th column\\
{\em d} & R & A maximal denominator needed for a dependence relation\\
}
\begin{aswhere}
Z &==& SingleInteger\\
\end{aswhere}
\Descr{
\name(a,p,st,c,r,d) backsolves a triangular system. $a,p$ and $st$
represent a matrix in REF. For $j\ge st(i)$ entry (i,j) of the REF is
stored in $a(p(i),j)$. $d$ must be such that $d$
times the $c$-th column of the REF is a linear combination of the
first $r$ leading columns of the REF (The $j$-th column is called
leading if $j=st(i)$ for some $i$). A vector $v$ is returned such that
$av=0$, the $c$-th coordinate of $v$ is $d$ and otherwise $v(j)\neq 0$
only if $j\le r$ and the $j$-th column is leading.
}
#endif

	backsolve: (M,ARR,ARR,SI,R,M) -> (M,PrimitiveArray R);
#if ASDOC
\aspage{backsolve}
\Usage{\name(a,p,st,r,d,b)}
\Signature{(M,PrimitiveArray Z,PrimitiveArray Z,Z,R,M)}{(M,PrimitiveArray R)}
\Params{
{\em a} & M & A matrix representing a Row Echelon Form (REF)\\
{\em p} & PrimitiveArray Z & A permutation of the rows of {\em a}\\
{\em st} & PrimitiveArray Z & The stairs of the REF\\
{\em r} & Z & The number of leading columns in $a$\\
{\em d} & R & A maximal denominator needed for a dependence relation\\
{\em b} & M & A matrix whose columns have to be backsolved\\
}
\begin{aswhere}
Z &==& SingleInteger\\
\end{aswhere}
\Descr{
\name(a,p,st,r,d,b) backsolves a triangular system. $a,p$ and $st$
represent a matrix in REF. For $j\ge st(i)$ entry (i,j) of the REF is
stored in $a(p(i),j)$. $d$ must be such that $d$
times the columns of $b$ are linear combinations of the
leading columns of the REF (The $j$-th column is called
leading if $j=st(i)$ for some $i$). A matrix $s$ and a PrimitiveArray $t$
are returned such that when $t(l)\neq 0$, then
$a$ times the $l$-th column of $s$ equals $d$ times the $l$-th column of
$b$, and when $t(l)=0$, then the $l$-th column of $b$ is not a linear
combination of the columns of $a$. $s(j,l)\neq 0$ only if the $j$-th column
is leading.
}
#endif

	if R has GcdDomain then {
		backsolve: (M,ARR,ARR,SI,SI) -> V;
#if ASDOC
\aspage{backsolve}
\Usage{\name(a,p,st,c,r)}
\Signature{(M,PrimitiveArray Z,PrimitiveArray Z,Z,Z)}{Vector R}
\Params{
{\em a} & M & A matrix representing a Row Echelon Form (REF)\\
{\em p} & PrimitiveArray Z & A permutation of the rows of {\em a}\\
{\em st} & PrimitiveArray Z & The stairs of the REF\\
{\em c} & Z & The column to be backsolved\\
{\em r} & Z & The number of leading columns before the $c$-th column\\
}
\begin{aswhere}
Z &==& SingleInteger\\
\end{aswhere}
\Descr{
\name(a,p,st,c,r) backsolves a triangular system in a minimal
way. $a,p$ and $st$ 
represent a matrix in REF. For $j\ge st(i)$ entry (i,j) of the REF is
stored in $a(p(i),j)$. A vector $v$ is returned such that
$av=0$, $v(j)\neq 0$ only if $j=c$ or $j\le r$ and the $j$-th
column is leading (The $j$-th column is called leading if $j=st(i)$
for some $i$) and the gcd of all entries of $v$ is 1.  
}
#endif

		backsolve: (M,ARR,ARR,SI,M) -> (M,PrimitiveArray R);
#if ASDOC
\aspage{backsolve}
\Usage{\name(a,p,st,r,b)}
\Signature{(M,PrimitiveArray Z,PrimitiveArray Z,Z,M)}{(M,PrimitiveArray R)}
\Params{
{\em a} & M & A matrix representing a Row Echelon Form (REF)\\
{\em p} & PrimitiveArray Z & A permutation of the rows of {\em a}\\
{\em st} & PrimitiveArray Z & The stairs of the REF\\
{\em r} & Z & The number of leading columns before the $c$-th column\\
{\em b} & M & A matrix whose columns have to be backsolved\\
}
\begin{aswhere}
Z &==& SingleInteger\\
\end{aswhere}
\Descr{
\name(a,p,st,r,b) backsolves a triangular system in a minimal
way. $a,p$ and $st$ 
represent a matrix in REF. For $j\ge st(i)$ entry (i,j) of the REF is
stored in $a(p(i),j)$.
A matrix $s$ and a PrimitiveArray $t$
are returned such that when $t(l)\neq 0$, then
$a$ times the $l$-th column of $s$ equals $t(l)$ times the $l$-th column of
$b$, and when $t(l)=0$, then the $l$-th column of $b$ is not a linear
combination of the columns of $a$. $s(j,l)\neq 0$ only if the $j$-th column
is leading (The $j$-th column is called leading if $j=st(i)$
for some $i$) and the gcd of all entries in the $l$-th column of $s$ and
$t(l)$ is 1.
}
#endif

		backsolve2: (M,ARR,ARR,SI,SI,R) -> V;
#if ASDOC
\aspage{backsolve2}
\Usage{\name(a,p,st,c,r,d)}
\Signature{(M,PrimitiveArray Z,PrimitiveArray Z,Z,Z,R)}{Vector R}
\Params{
{\em a} & M & A matrix representing a Row Echelon Form (REF)\\
{\em p} & PrimitiveArray Z & A permutation of the rows of {\em a}\\
{\em st} & PrimitiveArray Z & The stairs of the REF\\
{\em c} & Z & The column to be backsolved\\
{\em r} & Z & The number of leading columns before the
$c$-th column\\
{\em d} & R & A maximal denominator needed for a dependence relation\\
}
\begin{aswhere}
Z &==& SingleInteger\\
\end{aswhere}
\Descr{
\name(a,p,st,c,r,d) backsolves a triangular system in a minimal
way. $a,p$ and $st$ 
represent a matrix in REF. For $j\ge st(i)$ entry (i,j) of the REF is
stored in $a(p(i),j)$. A vector $v$ is returned such that
$av=0$, $v(j)\neq 0$ only if $j=c$ or $j\le r$ and the $j$-th
column is leading (The $j$-th column is called leading if $j=st(i)$
for some $i$) and the gcd of all entries of $v$ is 1.  
$d$ must be such that $d$ times the $c$-th column of the REF is a
linear combination of the first $r$ leading columns of the REF.
}
#endif

		backsolve2: (M,ARR,ARR,SI,R,M) -> (M,PrimitiveArray R);
#if ASDOC
\aspage{backsolve2}
\Usage{\name(a,p,st,r,d,b)}
\Signature{(M,PrimitiveArray Z,PrimitiveArray Z,Z,R,M)}{(M,PrimitiveArray R)}
\Params{
{\em a} & M & A matrix representing a Row Echelon Form (REF)\\
{\em p} & PrimitiveArray Z & A permutation of the rows of {\em a}\\
{\em st} & PrimitiveArray Z & The stairs of the REF\\
{\em r} & Z & The number of leading columns before the
$c$-th column\\
{\em d} & R & A maximal denominator needed for a dependence relation\\
{\em b} & M & A matrix whose columns have to be backsolved\\
}
\begin{aswhere}
Z &==& SingleInteger\\
\end{aswhere}
\Descr{
\name(a,p,st,r,d,b) backsolves a triangular system in a minimal
way. $a,p$ and $st$ 
represent a matrix in REF. For $j\ge st(i)$ entry (i,j) of the REF is
stored in $a(p(i),j)$. 
A matrix $s$ and a PrimitiveArray $t$
are returned such that when $t(l)\neq 0$, then
$a$ times the $l$-th column of $s$ equals $t(l)$ times the $l$-th column of
$b$, and when $t(l)=0$, then the $l$-th column of $b$ is not a linear
combination of the columns of $a$. $s(j,l)\neq 0$ only if the $j$-th column
is leading (The $j$-th column is called leading if $j=st(i)$
for some $i$) and the gcd of all entries in the $l$-th column of $s$ and
$t(l)$ is 1. 
$d$ must be such that $d$ times the columns of $b$ are 
linear combinations of the leading columns of the REF.
}
#endif
	}

} == add {

	backsolve(a:M,p:ARR,st:ARR,c:SI,r:SI,d:R): V == {
		m := cols a;
		v := zero m;
		v(c) := d;
		for i in r..1 by -1 repeat {
			e := -d*a(p(i),c);
			for j in i+1..r repeat
				e := e-a(p(i),st(j))*v(st(j));
			v(st(i)) := quotient(e,a(p(i),st(i)));
		}
		v;
	}

	backsolve(a:M,p:ARR,st:ARR,r:SI,d:R,b:M): (M,PrimitiveArray R) == {
		m := cols a;
		n := rows a;
		s := cols b;
		sol := zero(m,s);
		den:PrimitiveArray R := new(s,d);
		for k in 1..s repeat {
			for j in r+1..n repeat
				if b(p(j),k)~=0 then {
					den(k) := 0;
					break;
				}
			if den(k)=0 then
				iterate;
			for i in r..1 by -1 repeat {
				e := d*b(p(i),k);
				for j in i+1..r repeat
					e := e-a(p(i),st(j))*sol(st(j),k);
				sol(st(i),k) := quotient(e,a(p(i),st(i)));
			}
		}
		(sol,den);
	}

	if R has GcdDomain then {
		backsolve(a:M,p:ARR,st:ARR,c:SI,r:SI): V == {
			import from R,Partial R;
			if R has Field then
				return backsolve(a,p,st,c,r,1);
			m := cols a;
			v := zero m;
			v(c) := 1;
			for i in r..1 by -1 repeat {
				e := -v(c)*a(p(i),c);
				for j in i+1..r repeat
					e := e-a(p(i),st(j))*v(st(j));
				q := exactQuotient(e,a(p(i),st(i)));
				if failed? q then {
					(g,f1,f2) := gcdquo(e,a(p(i),st(i)));
					v(c) := f2*v(c);
					for j in i+1..r repeat
						v(st(j)) := f2*v(st(j));
					v(st(i)) := f1;
				}
				else
					v(st(i)) := retract q;
			}
			v;
		}

		backsolve(a:M,p:ARR,st:ARR,r:SI,b:M): (M,PrimitiveArray R) == {
			import from R,Partial R;
			if R has Field then
				return backsolve(a,p,st,r,1,b);
			m := cols a;
			n := rows a;
			s := cols b;
			sol := zero(m,s);
			den:PrimitiveArray R := new(s,1);
			for k in 1..s repeat {
				for j in r+1..n repeat
					if b(p(j),k)~=0 then {
						den(k) := 0;
						break;
					}
				if den(k)=0 then
					iterate;
				for i in r..1 by -1 repeat {
					e := den(k)*b(p(i),k);
					for j in i+1..r repeat
						e := e-a(p(i),st(j))*sol(st(j),k);
					q := exactQuotient(e,a(p(i),st(i)));
					if failed? q then {
						(g,f1,f2) := gcdquo(e,a(p(i),st(i)));
						den(k) := f2*den(k);
						for j in i+1..r repeat
							sol(st(j),k) := f2*sol(st(j),k);
						sol(st(i),k) := f1;
					}
					else
						sol(st(i),k) := retract q;
				}
			}
			(sol,den);
		}

		backsolve2(a:M,p:ARR,st:ARR,c:SI,r:SI,d:R): V == {
			import from List R;
			if R has Field then
				return backsolve(a,p,st,c,r,1);
			m := cols a;
			v := zero m;
			v(c) := d;
			for i in r..1 by -1 repeat {
				e := -d*a(p(i),c);
				for j in i+1..r repeat
					e := e-a(p(i),st(j))*v(st(j));
				v(st(i)) := quotient(e,a(p(i),st(i)));
			}
			l:List R := [v(st(i)) for i in 1..r];
			l := cons(v(c),l);
			g := gcd l;
			v(c) := quotient(v(c),g);
			for i in 1..r repeat
				v(st(i)) := quotient(v(st(i)),g);
			v;
		}

		backsolve2(a:M,p:ARR,st:ARR,r:SI,d:R,b:M): (M,PrimitiveArray R) == {
			import from List R;
			if R has Field then
				return backsolve(a,p,st,r,1,b);
			m := cols a;
			n := rows a;
			s := cols b;
			sol := zero(m,s);
			den:PrimitiveArray R := new(s,d);
			for k in 1..s repeat {
				for j in r+1..n repeat
					if b(p(j),k)~=0 then {
						den(k) := 0;
						break;
					}
				if den(k)=0 then
					iterate;
				for i in r..1 by -1 repeat {
					e := d*b(p(i),k);
					for j in i+1..r repeat
						e := e-a(p(i),st(j))*sol(st(j),k);
					sol(st(i),k) := quotient(e,a(p(i),st(i)));
				}
				l:List R := [sol(st(i),k) for i in 1..r];
				l := cons(den(k),l);
				g := gcd l;
				den(k) := quotient(den(k),g);
				for i in 1..r repeat
					sol(st(i),k) := quotient(sol(st(i),k),g);
			}
			(sol,den);
		}

	}
}
