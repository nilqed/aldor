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
------------------------------ sit_extpow.as ------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it ©INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I	== MachineInteger;
	Z	== Integer;
	V	== Vector;
	M	== DenseMatrix;
	ARR	== PrimitiveArray;
	EPP	== DenseHomogeneousExteriorProduct(n, m);
	EH	== DenseHomogeneousExteriorPower(R, n, m);

}

#if ALDOC
\thistype{ExteriorPower}
\History{Manuel Bronstein}{22/8/2000}{created}
\Usage{ import from \this(R, n, m) }
\Params{
{\em R} & \astype{IntegralDomain} & The coefficient domain\\
{\em n} & \astype{MachineInteger} & The power to compute\\
{\em m} & \astype{MachineInteger} & Order of the operator\\
}
\Descr{\this(R, n, m) provides functions that computes $\sth{n}$
exterior powers of operators of order $m$ having invertible
leading coefficients.}
\begin{exports}
\asexp{exteriorPower}:
& (\astype{PrimitiveArray} R, R $\to$ R) $\to$ \astype{Vector} R &
$\sth{n}$ exterior power\\
\end{exports}
#endif

ExteriorPower(R:IntegralDomain, n:I, m:I): with {
		exteriorPower: (ARR R, R -> R) -> V R;
#if ALDOC
\aspage{exteriorPower}
\Usage{\name($[a_0,\dots,a_{m-1}]$, $\sigma$)}
\Signature{(\astype{PrimitiveArray} R, R $\to$ R)}{\astype{Vector} R}
\Params{
$a_i$ & R & The coefficients of a monic difference operator\\
$\sigma$ & R $\to$ R & The shift morphism on R\\
}
\Retval{Returns $[v_1,\dots,v_N]$ such that the $\sth{n}$ exterior power of
$L = E^d - \sum_{i=0}^{d-1} a_i E^i$ is $\sum_{j=0}^{N-1} v_{j+1} E^j$.}
#endif
} == add {
	exteriorPower(a:ARR R, shift:R -> R):V R == {
		import from Z, R, EPP, EH, LinearAlgebra(R, M R);
		import from SymmetricPowerTools(R, R, n, m);
		EL := lift(shift, exteriorShift a);
		y := monomial(1, principalProduct);
		dim := machine(#$EPP);
		firstDependence(extCycle(EL, dim, y), dim);
	}

	local extCycle(E:EH -> EH, dim:I, y:EH):Generator V R == generate {
		import from V R;
		v := zero dim;
		vectorize!(v, y);
		yield v;
		repeat {
			y := E y;
			vectorize!(v, y);
			yield v;
		}
	}

	local vectorize!(v:V R, y:EH):V R == {
		for i in 1..#v repeat v.i := coefficient(y, i);
		v;
	}
}
