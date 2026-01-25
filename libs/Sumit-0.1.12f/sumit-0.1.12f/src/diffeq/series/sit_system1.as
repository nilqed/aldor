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
------------------------------ sit_system1.as ------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it ©INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I == MachineInteger;
	Z == Integer;
	M == DenseMatrix;
	V == Vector;
	RR == (R pretend GcdDomain);
	Q == Fraction RR;
	MOR == Automorphism;
}

#if ALDOC
\thistype{LinearOrdinaryFirstOrderSystem}
\History{Manuel Bronstein}{26/9/2000}{created}
\Usage{ import from \this~R}
\Params{
{\em R} & \astype{CommutativeRing} & The coefficient ring of the operators\\
}
\Descr{\this~R provides linear ordinary
systems of first order with coefficients in R.}
\begin{exports}
\asexp{matrix}:
& \% $\to$ (\astype{Vector} R, \astype{DenseMatrix} R) & Matrix representation\\
\asexp{order}: & \% $\to$ \astype{Integer} & Number of unknowns\\
\astype{system}: & \astype{DenseMatrix} R $\to$ \% & Create a system\\
                 & (R, \astype{DenseMatrix} R) $\to$ \% &\\
                 & (\astype{Vector} R, \astype{DenseMatrix} R) $\to$ \% &\\
\end{exports}
\begin{exports}[if $R$ has \astype{GcdDomain} then]
\asexp{changeVariable}:
& (\%, \astype{DenseMatrix} Q, \astype{Automorphism} Q, Q $\to$ Q &
Change of variable\\
\astype{system}: & \astype{DenseMatrix} Q $\to$ \% & Create a system\\
\end{exports}
\begin{exports}[if $R$ has \astype{Field} then]
\asexp{changeVariable}:
& (\%, \astype{DenseMatrix} R, \astype{Automorphism} R, R $\to$ R &
Change of variable\\
\end{exports}
\begin{aswhere}
Q &==& \astype{Fraction} R\\
\end{aswhere}
#endif

LinearOrdinaryFirstOrderSystem(R:CommutativeRing): with {
	if R has GcdDomain then {
		changeVariable: (%, M Q, Automorphism Q, Q -> Q) -> %;
	}
	if R has Field then {
		changeVariable: (%, M R, Automorphism R, R -> R) -> %;
	}
#if ALDOC
\aspage{changeVariable}
\Usage{\name($L,T,\sigma,\delta$)}
\Signatures{
\name:
& (\%, \astype{DenseMatrix} R, \astype{Automorphism} R, R $\to$ R) $\to$ \%\\
\name:
& (\%, \astype{DenseMatrix} Q, \astype{Automorphism} Q, Q $\to$ Q) $\to$ \%\\
}
\begin{aswhere}
Q &==& \astype{Fraction} R\\
\end{aswhere}
\Params{
{\em L} & \% & A system\\
{\em T} & \astype{DenseMatrix} R & An invertible matrix\\
        & \astype{DenseMatrix} \astype{Fraction} R & \\
$\sigma$ & \astype{Automorphism} R & The automorphism to use\\
         & \astype{Automorphism} \astype{Fraction} R & \\
$\delta$ & R $\to$ R & The $\sigma$-derivation to use\\
         & \astype{Fraction} R $\to$ \astype{Fraction} R & \\
}
\Retval{Returns a new system $\theta Z = M Z$ equivalent to
the original system $\theta Y = A Y$ under the change of variable 
$Y = T Z$.}
#endif
	matrix: % -> (V R, M R);
#if ALDOC
\aspage{matrix}
\Usage{\name~L}
\Signature{\%}{(\astype{Vector} R, \astype{DenseMatrix} R)}
\Params{ {\em L} & \% & A system\\ }
\Retval{Returns $([a_1,\dots,a_m], A)$ such that $L$ is the system
$$
\pmatrix{
a_1 & & \cr & \ddots & \cr & & a_m
}
\theta Y = A Y
$$
for some pseudo--linear operator $\theta$.}
#endif
	order: % -> Z;
#if ALDOC
\aspage{order}
\Usage{\name~L}
\Signature{\%}{Integer}
\Params{ {\em L} & \% & A system\\ }
\Retval{Returns the number of unknowns of $L$.}
#endif
	system: M R -> %;
	system: (R, M R) -> %;
	system: (V R, M R) -> %;
	if R has GcdDomain then {
		system: M Q -> %;
	}
#if ALDOC
\aspage{system}
\Usage{\name~A\\ \name~B\\ \name(a, A)\\ \name($[a_1,\dots,a_m]$, A)}
\Params{
{\em a}, $a_i$ & R & Coefficients\\
{\em A} & \astype{DenseMatrix} R & A square matrix\\
{\em B} & \astype{DenseMatrix} \astype{Fraction} R & A square matrix\\
}
\Retval{Return respectively the systems $\theta Y = A Y$,
$\theta Y = B Y$, $a \theta Y = A Y$ and
$$
\pmatrix{
a_1 & & \cr & \ddots & \cr & & a_m
}
\theta Y = A Y
$$
}
#endif
} == add {
	Rep == Record(coeff:V R, mat:M R);
	import from Rep;

	local coef(s:%):V R	== rep(s).coeff;
	local mat(s:%):M R	== rep(s).mat;
	matrix(s:%):(V R, M R)	== explode rep s;
	system(a:V R, m:M R):%	== { assert(square? m); per [a, m]; }
	order(s:%):Z		== { import from Z, M R; numberOfRows(mat s)::Z}
	system(m:M R):%		== { import from R; system(1, m); }

	system(a:R, m:M R):% == {
		import from V R;
		system(new(numberOfRows m, a), m);
	}

	if R has Field then {
		changeVariable(s:%, t:M R, sigma:MOR R, delta: R -> R):% == {
			import from I, R, Vector R, LinearAlgebra(R, M R);
			assert(square? t);
			n := numberOfRows t;
			(d, a) := matrix s;
			assert(n = numberOfColumns a);
			for i in 1..n repeat d.i := inv(d.i);
			d1 := diagonal d;
			(t1, dt1) := inverse(map(function sigma) t);
			system(t1 * d1 * a * t - t1 * map(delta) t);
		}
	}

	if R has GcdDomain then {
		changeVariable(s:%, t:M Q, sigma:MOR Q, delta: Q -> Q):% == {
			import from I, Q, Vector Q, LinearAlgebra(Q, M Q);
			import from MatrixCategoryOverFraction(RR,M RR,Q,M Q);
			assert(square? t);
			n := numberOfRows t;
			(d, A) := matrix s;
			assert(n = numberOfColumns A);
			d1 := diagonal [inv(f::Q) for f in d];
			a := d1 * makeRational A;
			(t1, dt1) := inverse(map(function sigma) t);
			system(t1 * a * t - t1 * map(delta) t);
		}

		system(m:M Q):% == {
			import from MatrixCategoryOverFraction(RR,M RR,Q,M Q);
			system makeRowIntegral m;
		}
	}
}
