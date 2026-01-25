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
------------------------------ sit_sptools.as ------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I	== MachineInteger;
	Z	== Integer;
	ARR	== PrimitiveArray;
	M	== DenseMatrix;
	PP      == DenseHomogeneousPowerProduct(n, m);
	H       == DenseHomogeneousPolynomial(R, n, m);
	EPP	== DenseHomogeneousExteriorProduct(n, m);
	EH	== DenseHomogeneousExteriorPower(R, n, m);

}

SymmetricPowerTools(S:IntegralDomain, R:IntegralDomain, n:I, m:I): with {
	exteriorDerivation: (ARR R, R) -> EPP -> EH;
	exteriorShift: ARR R -> EPP -> EH;
	inducedDerivation: (ARR R, R) -> PP -> H;
	exteriorPowerSystem: (EPP -> EH, R -> S) -> M S;
	symmetricPowerSystem: (PP -> H, R -> S) -> M S;
} == add {
	exteriorPowerSystem(D:EPP -> EH, f:R -> S):M S == {
		import from Z, EPP;
		dim := machine(#$EPP);
		mat:M S := zero(dim, dim);
		for i in 1..dim repeat vectorize!(mat, i, D lookup(i::Z), f);
		mat;
	}

	symmetricPowerSystem(D:PP -> H, f:R -> S):M S == {
		import from Z, PP;
		dim := machine(#$PP);
		mat:M S := zero(dim, dim);
		for i in 1..dim repeat vectorize!(mat, i, D lookup(i::Z), f);
		mat;
	}

	local vectorize!(mat:M S, i:I, y:H, f:R -> S):() == {
		for j in 1..numberOfColumns mat repeat
			mat(i, j) := f coefficient(y, j);
	}

	local vectorize!(mat:M S, i:I, y:EH, f:R -> S):() == {
		for j in 1..numberOfColumns mat repeat
			mat(i, j) := f coefficient(y, j);
	}

	-- must only code the shift on power products
	-- case where the leading coeff of L is invertible
	-- can then perform the calculations in R
	exteriorShift(a:ARR R):(EPP -> EH) == {
		m1 := prev m;
		mp1 := next m;
		(y:EPP):EH +-> {
			import from Boolean, Z, R, Partial EPP;
			~appears?(y, m) => monomial(1, retract increment y);
			q:EH := 0;
			for i in 0..m1 | ~zero?(a.i) repeat {
				(s, z) := incrementReplace(y, mp1, next i);
				if ~zero?(s) then q := add!(q, s::Z * a.i, z);
			}
			q;
		}
	}

	-- must only code the derivation on power products
	-- case where the leading coeff of L is invertible
	-- must only code the derivation on power products
	-- case where the leading coeff of L is invertible
	-- can then perform the calculations in R
	exteriorDerivation(a:ARR R, p:R):(EPP -> EH) == {
		m1 := prev m;
		(y:EPP):EH +-> {
			import from Boolean, Z, Partial EPP;
			q:EH := 0;
			for i in 1..n repeat {
				if ~failed?(u := increment(y, i)) then
					q := add!(q, p, retract u);
			}
			~appears?(y, m) => q;
			for i in 0..m1 | ~zero?(a.i) repeat {
				(s, z) := replace(y, m, next i);
				if ~zero?(s) then q := add!(q, s::Z * a.i, z);
			}
			q;
		}
	}

	-- must only code the derivation on power products
	-- case where the leading coeff of L is invertible
	-- can then perform the calculations in R
	inducedDerivation(a:ARR R, p:R):(PP -> H) == {
		m1 := prev m;
		(y:PP):H +-> {
			import from Boolean, Z;
			q:H := 0;
			for i in 1..m1 | (d := degree(y, i)) > 0 repeat
				q := add!(q, d::Z::R * p, incdec(y, next i, i));
			zero?(d := degree(y, m)) => q;
			e := d::Z;
			for i in 0..m1 | ~zero?(a.i) repeat
				q := add!(q, e * a.i, incdec(y, next i, m));
			q;
		}
	}
}
