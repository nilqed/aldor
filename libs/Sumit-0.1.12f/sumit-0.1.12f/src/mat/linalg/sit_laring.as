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
------------------------   sit_laring.as   -----------------------
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
\thistype{LinearAlgebraRing}
\History{Manuel Bronstein}{27/4/98}{created}
\Usage{this: Category}
\Descr{\this~is the category of rings that export algorithms for
linear algebra for matrices over themselves.}
\begin{exports}
\category{\astype{IntegralDomain}}\\
\asexp{determinant}: & (M:MC) $\to$ M $\to$ \% & Determinant\\
\asexp{factorOfDeterminant}:
& (M:MC) $\to$ M $\to$ (B, \%) & Probable determinant\\
\asexp{invertibleSubmatrix}:
& (M:MC) $\to$ M $\to$ (B, AZ, AZ) & Probable maximal minor\\
\asexp{inverse}: & (M:MC) $\to$ M $\to$ (M, V) & Inverse\\
\asexp{kernel}: & (M:MC) $\to$ M $\to$ M & Kernel\\
\asexp{linearDependence}:
& (\astype{Generator} V, Z) $\to$ V & First dependence relation\\
\asexp{maxInvertibleSubmatrix}:
& (M:MC) $\to$ M $\to$ (AZ, AZ) & Maximal minor\\
\asexp{particularSolution}: & (M:MC) $\to$ (M, M) $\to$ (M, V) & A solution\\
\asexp{rank}: & (M:MC) $\to$ M $\to$ Z & Rank\\
\asexp{rankLowerBound}:
& (M:MC) $\to$ M $\to$ (B, Z) & Probable rank\\
\asexp{solve}: & (M:MC) $\to$ (M, M) $\to$ (M, M, V) & All solutions\\
\asexp{span}: & (M:MC) $\to$ M $\to$ AZ & Span\\
\asexp{subKernel}: & (M:MC) $\to$ M $\to$ (B, M) & Subspace of the kernel\\
\end{exports}
\begin{aswhere}
AZ &==& \astype{Array} \astype{MachineInteger}\\
B &==& \astype{Boolean}\\
MC &==& \astype{MatrixCategory} \%\\
V &==& \astype{Vector} \%\\
Z &==& \astype{MachineInteger}\\
\end{aswhere}
#endif

define LinearAlgebraRing: Category == IntegralDomain with {
	determinant: (M:MatrixCategory %) -> M -> %;
#if ALDOC
\aspage{determinant}
\Usage{\name(M)(a)}
\Signature{(M:\astype{MatrixCategory} \%)}{M $\to$ R}
\Params{
{\em M} & \astype{MatrixCategory} \% & A matrix type\\
{\em a} & M & A matrix\\
}
\Retval{ Returns the determinant of {\em a}.}
\seealso{\asexp{factorOfDeterminant}}
#endif
	factorOfDeterminant: (M:MatrixCategory %) -> M -> (B, %);
#if ALDOC
\aspage{factorOfDeterminant}
\Usage{\name(M)(a)}
\Signature{(M:\astype{MatrixCategory} \%)}{M $\to$ (\astype{Boolean}, R)}
\Params{
{\em M} & \astype{MatrixCategory} \% & A matrix type\\
{\em a} & M & A matrix\\
}
\Retval{ Returns $(det?, d)$ such that $d$ is always a factor of
the determinant of {\em a}, and $d$ is exactly the determinant of $a$
if $det?$ is \true. }
\Remarks{$d$ can also happen to be the determinant of $a$ when $det?$ is
\false, but the algorithm was unable to prove it.}
\seealso{\asexp{determinant}}
#endif
	inverse: (M:MatrixCategory %) -> M -> (M, V %);
#if ALDOC
\aspage{inverse}
\Usage{\name(M)(a)}
\Signature{(M:\astype{MatrixCategory} \%)}{M $\to$ (M, \astype{Vector} R)}
\Params{
{\em M} & \astype{MatrixCategory} \% & A matrix type\\
{\em a} & M & A matrix\\
}
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
When $R$ is a \astype{Field}, then $d_i \in \{0,1\}$ for $1 \le i \le n$,
so $b = a^{-1}$ when $R$ is a \astype{Field} and $a$ is invertible.}
#endif
	invertibleSubmatrix: (M:MatrixCategory %) -> M -> (B, A I, A I);
#if ALDOC
\aspage{invertibleSubmatrix}
\Usage{\name(M)(a)}
\Signature{(M:\astype{MatrixCategory} \%)}{M $\to$ (\astype{Boolean}, AZ, AZ)}
\begin{aswhere}
AZ &==& \astype{Array} \astype{MachineInteger}\\
\end{aswhere}
\Params{
{\em M} & \astype{MatrixCategory} \% & A matrix type\\
{\em a} & M & A matrix\\
}
\Retval{ Returns $(max?, [r_1,\dots,r_r], [c_1,\dots,c_r])$
where $r \le \mbox{rank}(a)$
and the submatrix of $a$ formed by the intersections of the rows $r_i$
and $c_i$ is always invertible. If $max?$ is \true, then $r$ is exactly
the rank of $a$ and the given minor is of maximal size.}
\Remarks{$r$ can also happen to be the rank of $a$ when $max?$ is \false,
but the algorithm was unable to prove it.}
\seealso{\asexp{maxInvertibleSubmatrix}}
#endif
	kernel: (M:MatrixCategory %) -> M -> M;
#if ALDOC
\aspage{kernel}
\Usage{\name(M)(a)}
\Signature{(M:\astype{MatrixCategory} \%)}{M $\to$ M}
\Params{
{\em M} & \astype{MatrixCategory} \% & A matrix type\\
{\em a} & M & A matrix\\
}
\Retval{ Returns a matrix whose columns form a basis of the kernel of {\em a}.}
\seealso{\asexp{solve},\asexp{subKernel}}
#endif
	linearDependence: (Generator V %, I) -> V %;
#if ALDOC
\aspage{linearDependence}
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
independent. The dimension of the vectors generated by {\em gen} must be
{\em n}. There must be a relation between the vectors generated.
}
#endif
	maxInvertibleSubmatrix: (M:MatrixCategory %) -> M -> (A I, A I);
#if ALDOC
\aspage{maxInvertibleSubmatrix}
\Usage{\name(M)(a)}
\Signature{(M:\astype{MatrixCategory} \%)}{M $\to$ (AZ, AZ)}
\begin{aswhere}
AZ &==& \astype{Array} \astype{MachineInteger}\\
\end{aswhere}
\Params{
{\em M} & \astype{MatrixCategory} \% & A matrix type\\
{\em a} & M & A matrix\\
}
\Retval{ Returns $([r_1,\dots,r_r], [c_1,\dots,c_r])$
where $r$ is the rank of {\em a}
and the submatrix of $a$ formed by the intersections of the rows $r_i$
and $c_i$ is invertible.}
\seealso{\asexp{invertibleSubmatrix}}
#endif
	particularSolution: (M:MatrixCategory %) -> (M, M) -> (M, V %);
#if ALDOC
\aspage{particularSolution}
\Usage{\name(M)(a, b)}
\Signature{(M:\astype{MatrixCategory} \%)}{(M, M) $\to$ (M, \astype{Vector} R)}
\Params{
{\em M} & \astype{MatrixCategory} \% & A matrix type\\
{\em a, b} & M & Matrices\\
}
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
	rank: (M:MatrixCategory %) -> M -> I;
#if ALDOC
\aspage{rank}
\Usage{\name(M)(a)}
\Signature{(M:\astype{MatrixCategory} \%)}{M $\to$ \astype{MachineInteger}}
\Params{
{\em M} & \astype{MatrixCategory} \% & A matrix type\\
{\em a} & M & A matrix\\
}
\Retval{ Returns the rank of {\em a}.  }
\seealso{\asexp{rankLowerBound},\asexp{span}}
#endif
	rankLowerBound: (M:MatrixCategory %) -> M -> (B, I);
#if ALDOC
\aspage{rank}
\Usage{\name(M)(a)}
\Signature{(M:\astype{MatrixCategory} \%)}{M $\to$ \astype{MachineInteger}}
\Params{
{\em M} & \astype{MatrixCategory} \% & A matrix type\\
{\em a} & M & A matrix\\
}
\Retval{ Returns $(rank?, r)$ such that $r \le \mbox{rank}(a)$,
and $r$ is exactly the rank of $a$ if $rank?$ is \true. }
\seealso{\asexp{rankLowerBound},\asexp{span}}
#endif
	rankLowerBound: (M:MatrixCategory %) -> M -> (B, I);
#if ALDOC
\aspage{rankLowerBound}
\Usage{\name(M)(a)}
\Signature{(M:\astype{MatrixCategory} \%)}{M $\to$ (\astype{Boolean}, \astype{MachineInteger})}
\Params{
{\em M} & \astype{MatrixCategory} \% & A matrix type\\
{\em a} & M & A matrix\\
}
\Retval{ Returns $(rank?, r)$ such that $r \le \mbox{rank}(a)$,
and $r$ is exactly the rank of $a$ if $rank?$ is \true. }
\Remarks{$r$ can also happen to be the rank of $a$ when $rank?$ is \false,
but the algorithm was unable to prove it.}
\seealso{\asexp{rank},\asexp{span}}
#endif
	solve: (M:MatrixCategory %) -> (M, M) -> (M, M, V %);
#if ALDOC
\aspage{solve}
\Usage{\name(M)(a, b)}
\Signature{(M:\astype{MatrixCategory} \%)}{(M, M) $\to$ (M, M, \astype{Vector} R)}
\Params{
{\em M} & \astype{MatrixCategory} \% & A matrix type\\
{\em a, b} & M & Matrices\\
}
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
	span: (M:MatrixCategory %) -> M -> A I;
#if ALDOC
\aspage{span}
\Usage{\name(M)(a)}
\Signature{(M:\astype{MatrixCategory} \%)}{M $\to$ \astype{Array} \astype{MachineInteger}}
\Params{
{\em M} & \astype{MatrixCategory} \% & A matrix type\\
{\em a} & M & A matrix\\
}
\Retval{ Returns $[c_1,\dots,c_r]$ where $r$ is the rank of {\em a}
and the span of $a$ is generated by its columns $c_1,\dots,c_r$.}
\seealso{\asexp{rank}}
#endif
	subKernel: (M:MatrixCategory %) -> M -> (B, M);
#if ALDOC
\aspage{subKernel}
\Usage{\name(M)(a)}
\Signature{(M:\astype{MatrixCategory} \%)}{M $\to$ (\astype{Boolean}, M)}
\Params{
{\em M} & \astype{MatrixCategory} \% & A matrix type\\
{\em a} & M & A matrix\\
}
\Retval{ Returns $(ker?, m)$ such that the columns of $m$, which are always
linearly independent over R, generate a subspace of the kernel of $a$,
and generate the full kernel if $ker?$ is \true.}
\Remarks{$m$ can also happen to generate the full kernel of $a$ when $ker?$ is
\false, but the algorithm was unable to prove it.}
\seealso{\asexp{kernel}}
#endif
	default {
		factorOfDeterminant(M:MatrixCategory %):M -> (B, %) == {
			(m:M):(B, %) +-> (true, determinant(M)(m));
		}

		rankLowerBound(M:MatrixCategory %):M -> (B, I) == {
			(m:M):(B, I) +-> (true, rank(M)(m));
		}

		invertibleSubmatrix(M:MatrixCategory %):M -> (B, A I, A I) == {
			(m:M):(B, A I, A I) +-> {
				(r, c) := maxInvertibleSubmatrix(M)(m);
				(true, r, c);
			}
		}

		subKernel(M:MatrixCategory %):M -> (B, M) == {
			(m:M):(B, M) +-> (true, kernel(M)(m));
		}
	}
}
