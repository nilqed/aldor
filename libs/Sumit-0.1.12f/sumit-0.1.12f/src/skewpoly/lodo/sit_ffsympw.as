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
------------------------------ sit_ffsympw.as ------------------------------
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
	PP	== DenseHomogeneousPowerProduct(n, m);
	EPP	== DenseHomogeneousExteriorProduct(n, m);
	Rp	== FractionBy(R, P, irr?);
	H	== DenseHomogeneousPolynomial(Rp, n, m);
	EH	== DenseHomogeneousExteriorPower(Rp, n, m);
}

-- m = order of the operator
-- n = symmetric power to compute
-- This code should not be used for 2nd order operators, for which
--   SecondOrderSymmetricPower is more appropriate
-- This code should not be called if P is a unit in R, for which
--   SymmetricPower  is more appropriate
FactorFreeSymmetricPower(R:IntegralDomain,
		Rd:LinearOrdinaryDifferentialOperatorCategory0 R,
		n:I, m:I, P:R, irr?:Boolean): with {
			exteriorPower: Rd -> Rd;
			symmetricPower: Rd -> Rd;
			exteriorPowerSystem: Rd -> (R, M R);
			symmetricPowerSystem: Rd -> (R, M R);
} == add {
	-- must only code the derivation on power products
	-- case where the leading coeff p of L is not invertible
	-- computes then p times the induced derivation
	local exteriorDerivation(L:Rd, p:R):(EPP -> EH) == {
		import from Z, Rp, ARR Rp, SymmetricPowerTools(R, Rp, n, m);
		a:ARR Rp := new m;
		for i in 0..prev m repeat
			a.i := - normalize(coefficient(L, i::Z)::Rp);
		exteriorDerivation(a, shift(1@Rp, 1));
	}

	-- must only code the derivation on power products
	-- case where the leading coeff p of L is not invertible
	-- computes then p times the induced derivation
	local inducedDerivation(L:Rd, p:R):(PP -> H) == {
		import from Z, Rp, ARR Rp, SymmetricPowerTools(R, Rp, n, m);
		a:ARR Rp := new m;
		for i in 0..prev m repeat
			a.i := - normalize(coefficient(L, i::Z)::Rp);
		inducedDerivation(a, shift(1@Rp, 1));
	}

	-- case where the leading coeff p of L is not invertible
	-- uses then p times the induced derivation
	symmetricPowerSystem(L:Rd):(R, M R) == {
		import from Rp, SymmetricPowerTools(R, Rp, n, m);
		p := leadingCoefficient L;
		(p, symmetricPowerSystem(inducedDerivation(L, p), numerator));
	}

	-- case where the leading coeff p of L is not invertible
	-- uses then p times the exterior derivation
	exteriorPowerSystem(L:Rd):(R, M R) == {
		import from Rp, SymmetricPowerTools(R, Rp, n, m);
		p := leadingCoefficient L;
		(p, exteriorPowerSystem(exteriorDerivation(L, p), numerator));
	}

	-- case where the leading coeff p of Rd is not invertible
	-- uses then p times the induced derivation
	symmetricPower(L:Rd):Rd == { 
		import from Z, Rp, Derivation R, Derivation Rp, H;
		import from FractionFreeCyclicVector(R, P, irr?);
		TRACE("ffsympw::symmetricPower: L = ", L);
		p := leadingCoefficient L;
		TRACE("ffsympw::symmetricPower: p = ", p);
		D := derivation$Rd;
		DRp := lift D;
		pD := derivation((x:Rp):Rp +-> shift(DRp x, 1));
		TRACE("ffsympw::symmetricPower: ", "pD computed");
		DL := lift(pD, inducedDerivation(L, p));
		TRACE("ffsympw::symmetricPower: ", "DL computed");
		firstDependence(makeMatrix(D(p)::Rp, DL))::Rd;
	}

	-- case where the leading coeff p of L is not invertible
	-- uses then p times the exterior derivation
	exteriorPower(L:Rd):Rd == { 
		import from Z, Rp, Derivation R, Derivation Rp, EH;
		import from FractionFreeCyclicVector(R, P, irr?);
		p := leadingCoefficient L;
		D := derivation$Rd;
		DRp := lift D;
		pD := derivation((x:Rp):Rp +-> shift(DRp x, 1));
		DL := lift(pD, exteriorDerivation(L, p));
		firstDependence(makeExtMatrix(D(p)::Rp, DL))::Rd;
	}

	-- D is already p times the induced derivation
	local makeMatrix(Dp:Rp, D:H -> H):M Rp == {
		import from Z, PP, H;
		nu:Z := 0;
		dim := machine(#$PP);
		mat := zero(dim, next dim);
		y := monomial(1, monomial 1);
		for i in 1..dim repeat {
			vectorize!(mat, i, y);
			Dy := D y;	-- always a new copy
			y  := add!(Dy, times!(nu * Dp, y));
			nu := prev nu;
		}
		vectorize!(mat, next dim, y);
		mat;
	}

	-- D is already p times the exterior derivation
	local makeExtMatrix(Dp:Rp, D:EH -> EH):M Rp == {
		import from Z, EPP, EH;
		nu:Z := 0;
		dim := machine(#$EPP);
		mat := zero(dim, next dim);
		y := monomial(1, principalProduct);
		for i in 1..dim repeat {
			vectorize!(mat, i, y);
			Dy := D y;	-- always a new copy
			y  := add!(Dy, times!(nu * Dp, y));
			nu := prev nu;
		}
		vectorize!(mat, next dim, y);
		mat;
	}

	local vectorize!(mat:M Rp, j:I, y:H):() == {
		dim := numberOfRows mat;
		for i in 1..dim repeat mat(dim + 1 - i, j) := coefficient(y, i);
	}

	local vectorize!(mat:M Rp, j:I, y:EH):() == {
		dim := numberOfRows mat;
		for i in 1..dim repeat mat(dim + 1 - i, j) := coefficient(y, i);
	}
}
