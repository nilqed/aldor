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
------------------------------ sit_sympow.as ------------------------------
-- Copyright (c) Manuel Bronstein 1997
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1997
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I	== MachineInteger;
	Z	== Integer;
	V	== Vector;
	M	== DenseMatrix;
	ARR	== PrimitiveArray;
	PP      == DenseHomogeneousPowerProduct(n, m);
	H       == DenseHomogeneousPolynomial(R, n, m);
	EPP	== DenseHomogeneousExteriorProduct(n, m);
	EH	== DenseHomogeneousExteriorPower(R, n, m);

}

#if ALDOC
\thistype{SymmetricPower}
\History{Manuel Bronstein}{14/1/97}{created}
\Usage{ import from \this(R, Rd, n, m) }
\Params{
{\em R} & \astype{IntegralDomain} & The coefficient domain\\
{\em Rd} & \astype{LinearOrdinaryDifferentialOperatorCategory0} R &
A LODO type over R\\
{\em n} & \astype{MachineInteger} & The power to compute\\
{\em m} & \astype{MachineInteger} & Order of the operator\\
}
\Descr{\this(R, Rd, n, m) provides a function that computes $\sth{n}$
exterior and symmetric powers of operators of order $m$ having invertible
leading coefficients.
This package should not be used for $m=2$,
for which a faster algorithm is provided by
\astype{SecondOrderSymmetricPower}.
Use \astype{FractionFreeSymmetricPower} for operators of order at least $3$
whose leading coefficients are not invertible in $R$.}
\begin{exports}
\asexp{exteriorPower}: & (Rd, R) $\to$ Rd & $\sth{n}$ exterior power\\
\asexp{exteriorPowerSystem}:
& (Rd, R) $\to$ \astype{DenseMatrix} R & $\sth{n}$ exterior power\\
\asexp{symmetricPower}: & (Rd, R) $\to$ Rd & $\sth{n}$ symmetric power\\
\asexp{symmetricPowerSystem}:
& (Rd, R) $\to$ \astype{DenseMatrix} R & $\sth{n}$ symmetric power\\
\end{exports}
#endif

SymmetricPower(R:IntegralDomain,
	Rd:LinearOrdinaryDifferentialOperatorCategory0 R, n:I, m:I): with {
		exteriorPower: (Rd, R) -> Rd;
		symmetricPower: (Rd, R) -> Rd;
#if ALDOC
\aspage{exteriorPower,symmetricPower}
\astarget{exteriorPower}
\astarget{symmetricPower}
\Usage{exteriorPower(L, a)\\ symmetricPower(L, a)}
\Signature{(Rd,R)}{Rd}
\Params{
{\em L} & Rd & A differential operator of order $m$\\
{\em a} & R & The inverse of the leading coefficient of $L$\\
}
\Retval{Return respectively the $\sth{n}$ exterior and symmetric power
of $L$.}
#endif
		exteriorPowerSystem: (Rd, R) -> M R;
		symmetricPowerSystem: (Rd, R) -> M R;
#if ALDOC
\aspage{exteriorPowerSystem,symmetricPowerSystem}
\astarget{exteriorPowerSystem}
\astarget{symmetricPowerSystem}
\Usage{exteriorPowerSystem(L, a)\\ symmetricPowerSystem(L, a)}
\Signature{(Rd,R)}{\astype{DenseMatrix} R}
\Params{
{\em L} & Rd & A differential operator of order $m$\\
{\em a} & R & The inverse of the leading coefficient of $L$\\
}
\Retval{Return a matrix $M$ such that the differential system
$Y' = M Y$ is respectively the $\sth{n}$ exterior and symmetric power system
of $L$.}
#endif
} == add {
	local identity(r:R):R == r;

	-- must only code the derivation on power products
	-- case where the leading coeff of L is invertible
	-- ainv = inverse of leading coeff
	-- can then perform the calculations in R
	local exteriorDerivation(L:Rd, ainv:R):(EPP -> EH) == {
		import from Z, ARR R, SymmetricPowerTools(R, R, n, m);
		a:ARR R := new m;
		for i in 0..prev m repeat a.i := - ainv * coefficient(L, i::Z);
		exteriorDerivation(a, 1);
	}

	-- must only code the derivation on power products
	-- case where the leading coeff of L is invertible
	-- ainv = inverse of leading coeff
	-- can then perform the calculations in R
	local inducedDerivation(L:Rd, ainv:R):(PP -> H) == {
		import from Z, ARR R, SymmetricPowerTools(R, R, n, m);
		a:ARR R := new m;
		for i in 0..prev m repeat a.i := - ainv * coefficient(L, i::Z);
		inducedDerivation(a, 1);
	}

	-- case where the leading coeff of L is invertible
	-- ainv = inverse of leading coeff
	-- can then perform the calculations in R
	symmetricPowerSystem(L:Rd, ainv:R):M R == {
		import from SymmetricPowerTools(R, R, n, m);
		assert(one?(ainv * leadingCoefficient L));
		symmetricPowerSystem(inducedDerivation(L, ainv), identity);
	}

	-- case where the leading coeff of L is invertible
	-- ainv = inverse of leading coeff
	-- can then perform the calculations in R
	exteriorPowerSystem(L:Rd, ainv:R):M R == {
		import from SymmetricPowerTools(R, R, n, m);
		assert(one?(ainv * leadingCoefficient L));
		exteriorPowerSystem(exteriorDerivation(L, ainv), identity);
	}

	-- case where the leading coeff of L is invertible
	-- ainv = inverse of leading coeff
	-- can then perform the calculations in R
	symmetricPower(L:Rd, ainv:R):Rd == {
		import from Z, PP, H, LinearAlgebra(R, M R);
		assert(one?(ainv * leadingCoefficient L));
		DL := lift(derivation, inducedDerivation(L, ainv));
		y := monomial(1, monomial 1);
		dim := machine(#$PP);
		firstDependence(symCycle(DL, dim, y), dim)::Rd;
	}

	local symCycle(D:H -> H, dim:I, y:H):Generator V R == generate {
		import from V R;
		v := zero dim;
		vectorize!(v, y);
		yield v;
		repeat {
			y := D y;
			vectorize!(v, y);
			yield v;
		}
	}

	-- case where the leading coeff of L is invertible
	-- ainv = inverse of leading coeff
	-- can then perform the calculations in R
	exteriorPower(L:Rd, ainv:R):Rd == {
		import from Z, EPP, EH, LinearAlgebra(R, M R);
		assert(one?(ainv * leadingCoefficient L));
		DL := lift(derivation, exteriorDerivation(L, ainv));
		y := monomial(1, principalProduct);
		dim := machine(#$EPP);
		firstDependence(extCycle(DL, dim, y), dim)::Rd;
	}

	local extCycle(D:EH -> EH, dim:I, y:EH):Generator V R == generate {
		import from V R;
		v := zero dim;
		vectorize!(v, y);
		yield v;
		repeat {
			y := D y;
			vectorize!(v, y);
			yield v;
		}
	}

	local vectorize!(v:V R, y:H):V R == {
		for i in 1..#v repeat v.i := coefficient(y, i);
		v;
	}

	local vectorize!(v:V R, y:EH):V R == {
		for i in 1..#v repeat v.i := coefficient(y, i);
		v;
	}
}
