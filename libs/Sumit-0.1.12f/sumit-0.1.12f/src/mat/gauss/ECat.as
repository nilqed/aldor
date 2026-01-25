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
------------------------------ ECat.as ------------------------------------
#include "sumit"

#if ASDOC
\thistype{EliminationCategory}
\History{Thom Mulders}{8 July 96}{created}
\Usage{\this(R,M): Category}
\Params{
{\em R} & CommutativeRing & A coefficient ring\\
{\em M} & MatrixCategory0 R& A matrix type over R\\
}
\Descr{\this~is a common category for linear elimination computations.
The category provides operations for computating a row echelon form
(REF) of a matrix and the first dependence relation among vectors.}
\begin{exports}
denominators: & (M,ARR,Z,ARR) $\to$ PrimitiveArray R & Maximal denominators\\ 
dependence: & (Generator V,Z) $\to$ (M,ARR,Z,R) & First dependence relation\\
deter: & (M,ARR,Z,ARR) $\to$ R & Determinant of a matrix\\
extendedRowEchelon: & M $\to$ (M,ARR,Z,ARR,Z,M) & REF of a matrix\\
extendedRowEchelon!: & M $\to$ (ARR,Z,ARR,Z,M) & REF of a matrix\\
rowEchelon: & M $\to$ (M,ARR,Z,ARR,Z) & REF of a matrix\\
rowEchelon!: & M $\to$ (ARR,Z,ARR,Z) & REF of a matrix\\
\end{exports}
\Aswhere{
Z & == & SingleInteger\\
ARR & == & PrimitiveArray SI\\
V & == & Vector R\\
}
#endif

macro SI == SingleInteger;
macro ARR == PrimitiveArray SI;
macro V == Vector R;

EliminationCategory(R:CommutativeRing, M:MatrixCategory0 R): Category == with {
	denominators: (M,ARR,SI,ARR) -> PrimitiveArray R;
#if ASDOC
\aspage{denominators}
\Usage{\name(a,p,r,st)}
\Signature{(M,PrimitiveArray Z,Z, PrimitiveArray Z)}{PrimitiveArray R}
\Aswhere{ Z & == & SingleInteger\\ }
\Params{
{\em a} & M & A matrix representing a REF of a matrix\\
{\em p} & PrimitiveArray SingleInteger & A permutation of the rows of {\em a}\\
{\em r} & SingleInteger & The number of stairs of the REF\\
{\em st} & PrimitiveArray SingleInteger & The stairs of the REF\\
}
\Descr{
{\em (a,p,r,st)} must be the representation of a REF computed by {\em
rowEchelon}, {\em extendedRowEchelon} or their bang-versions. When
{\em d} is returned then for $st(i)<j<st(i+1)$ we have that $d(i)$ times the
$j$-th column of the REF is a linear combination of the first $i$
leading columns of the REF. (The $i$-th column is called leading if
$i$ is a stair) 
}
#endif
	dependence: (Generator V,SI) -> (M,ARR,SI,R);
#if ASDOC
\aspage{dependence}
\Usage{\name(gen,n)}
\Signature{(Generator V,Z)}{(M,PrimitiveArray Z,Z,R)}
\Aswhere{ Z & == & SingleInteger\\ }
\Params{
{\em gen} & Generator V & A generator of vectors\\
{\em n} & SingleInteger & The dimension of the vectors generated\\
}
\Descr{
\name(gen,n) computes the first dependence among the vectors
generated. First means that \name(gen,n) stops as soon as a dependence
relation exists among the vectors generated so far. \name(gen,n)
returns a matrix {\em a}, a permutation {\em p}, the length {\em r} of a
relation and the maximal denominator {\em d} needed for a dependence
relation. After applying {\em p} to the rows of {\em a} one gets a
matrix whose first $r-1$ columns form an upper-triangular
matrix. $d$ times the last column of $a$ is a linear combination of
the first $r-1$ columns of $a$. A dependence relation between the
columns of $a$ is also a dependence relation between the vectors
generated. 
}
#endif
	deter: (M,ARR,SI,ARR,SI) -> R;
#if ASDOC
\aspage{deter}
\Usage{\name(a,p,r,st,d)}
\Signature{(M,PrimitiveArray Z,Z, PrimitiveArray Z,Z)}{R}
\Aswhere{ Z & == & SingleInteger\\ }
\Params{
{\em a} & M & A matrix representing a REF of a matrix\\
{\em p} & PrimitiveArray SingleInteger & A permutation of the rows of {\em a}\\
{\em r} & SingleInteger & The number of stairs of the REF\\
{\em st} & PrimitiveArray SingleInteger & The stairs of the REF\\
{\em d} & SingleInteger & The sign of p\\
}
\Descr{
{\em (a,p,r,st,d)} must be the representation of a REF computed by {\em
rowEchelon}, {\em extendedRowEchelon} or their bang-versions. The
determinant of the original matrix is returned. 
}
#endif
	extendedRowEchelon: M -> (M,ARR,SI,ARR,SI,M);
#if ASDOC
\aspage{extendedRowEchelon}
\Usage{\name~a}
\Signature{M}{(M,PrimitiveArray Z,Z,PrimitiveArray Z,Z,M)} 
\Aswhere{ Z & == & SingleInteger\\ }
\Params{
{\em a} & M & A matrix whose REF and corresponding transformation matrix\\
& &  have to be computed\\
}
\Descr{
We say that a matrix $a$ is in REF if there are $r$ (the rank) and
$j_1<j_2<\cdots<j_r$ (the stairs) such that $a(i,j_i)\neq 0$,
$a(i,j)=0$ for $j<j_i$ and $a(i,j)=0$ for $i>r$.

We say that a matrix $b$ is a REF of the matrix $a$ if $b$ is in REF
and there exists a non-singular matrix $u$ such that $ua=b$.

\bigskip
\name~a computes a REF of {\em a} in {\em a}. It returns {\em (c,p,r,st,d,w)}
where {\em c} is a matrix, {\em p} is a permutation, {\em r} is the
number of stairs, {\em 
st} are the stairs, {\em d} is the sign of {\em p} and {\em w} is a matrix.
For $i > r$, {\em st(i)} is set to $m+1$ where $m$ is the number of columns
of {\em a}.
For $j\ge j_i$ the entry $(i,j)$ of the REF is stored as entry
$(p(i),j)$ in {\em c}. The other entries of {\em c} may have random
values.
The entry $(i,j)$ of the transformation matrix {\em u} is stored as
entry $(p(i),j)$ in {\em w}.
}
#endif
	extendedRowEchelon!: M -> (ARR,SI,ARR,SI,M);
#if ASDOC
\aspage{extendedRowEchelon!}
\Usage{\name~a}
\Signature{M}{(PrimitiveArray Z,Z,PrimitiveArray Z,Z,M)} 
\Aswhere{ Z & == & SingleInteger\\ }
\Params{
{\em a} & M & A matrix whose REF and corresponding transformation matrix\\
& &  have to be computed\\
}
\Descr{
We say that a matrix $a$ is in REF if there are $r$ (the rank) and
$j_1<j_2<\cdots<j_r$ (the stairs) such that $a(i,j_i)\neq 0$,
$a(i,j)=0$ for $j<j_i$ and $a(i,j)=0$ for $i>r$.

We say that a matrix $b$ is a REF of the matrix $a$ if $b$ is in REF
and there exists a non-singular matrix $u$ such that $ua=b$.

\bigskip
\name~a computes a REF of {\em a} in {\em a}. It returns {\em (p,r,st,d,w)}
where {\em p} is a permutation, {\em r} is the number of stairs, {\em
st} are the stairs, {\em d} is the sign of {\em p} and {\em w} is a matrix.
For $i > r$, {\em st(i)} is set to $m+1$ where $m$ is the number of columns
of {\em a}.
For $j\ge j_i$ the entry $(i,j)$ of the REF is stored as entry
$(p(i),j)$ in {\em a}. The other entries of {\em a} may have random
values.
The entry $(i,j)$ of the transformation matrix {\em u} is stored as
entry $(p(i),j)$ in {\em w}.
}
#endif
	rowEchelon: M -> (M,ARR,SI,ARR,SI);
#if ASDOC
\aspage{rowEchelon}
\Usage{\name~a}
\Signature{M}{(M,PrimitiveArray Z,Z,PrimitiveArray Z,Z)} 
\Aswhere{ Z & == & SingleInteger\\ }
\Params{ {\em a} & M & A matrix whose REF has to be computed\\ }
\Descr{
We say that a matrix $a$ is in REF if there are $r$ (the rank) and
$j_1<j_2<\cdots<j_r$ (the stairs) such that $a(i,j_i)\neq 0$,
$a(i,j)=0$ for $j<j_i$ and $a(i,j)=0$ for $i>r$.

We say that a matrix $b$ is a REF of the matrix $a$ if $b$ is in REF
and there exists a non-singular matrix $u$ such that $ua=b$.

\bigskip
\name~a computes a REF of {\em a}. It returns {\em (c,p,r,st,d)}
where {\em c} is a matrix, {\em p} is a permutation, {\em r} is the
number of stairs, {\em st} are the stairs and {\em d} is the sign of {\em p}.
For $i > r$, {\em st(i)} is set to $m+1$ where $m$ is the number of columns
of {\em a}.
For $j\ge j_i$ the entry $(i,j)$ of the REF is stored as entry
$(p(i),j)$ in {\em c}. The other entries of {\em c} may have random values.
}
#endif
	rowEchelon!: M -> (ARR,SI,ARR,SI);
#if ASDOC
\aspage{rowEchelon!}
\Usage{\name~a}
\Signature{M}{(PrimitiveArray Z,Z,PrimitiveArray Z,Z)} 
\Aswhere{ Z & == & SingleInteger\\ }
\Params{ {\em a} & M & A matrix whose REF has to be computed\\ }
\Descr{
We say that a matrix $a$ is in REF if there are $r$ (the rank) and
$j_1<j_2<\cdots<j_r$ (the stairs) such that $a(i,j_i)\neq 0$,
$a(i,j)=0$ for $j<j_i$ and $a(i,j)=0$ for $i>r$.

We say that a matrix $b$ is a REF of the matrix $a$ if $b$ is in REF
and there exists a non-singular matrix $u$ such that $ua=b$.

\bigskip
\name~a computes a REF of {\em a} in {\em a}. It returns {\em (p,r,st,d)}
where {\em p} is a permutation, {\em r} is the number of stairs, {\em
st} are the stairs and {\em d} is the sign of {\em p}.
For $i > r$, {\em st(i)} is set to $m+1$ where $m$ is the number of columns
of {\em a}.
For $j\ge j_i$ the entry $(i,j)$ of the REF is stored as entry
$(p(i),j)$ in {\em a}. The other entries of {\em a} may have random values.
}
#endif
	default {
		rowEchelon(a:M): (M,ARR,SI,ARR,SI) == {
			copya := copy a;
			(p,r,st,d) := rowEchelon!(copya);
			(copya,p,r,st,d);
		}

		extendedRowEchelon(a:M): (M,ARR,SI,ARR,SI,M) == {
			copya := copy a;
			(p,r,st,d,t) := extendedRowEchelon!(copya);
			(copya,p,r,st,d,t);
		}
	}
}
