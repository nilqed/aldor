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
------------------------------ ffsympow.as ------------------------------
#include "sumit"

macro {
	I	== SingleInteger;
	Z	== Integer;
	V	== Vector;
	M	== DenseMatrix;
	ARR	== PrimitiveArray;
	PP	== DenseHomogeneousPowerProduct(n, m);
	EPP	== DenseHomogeneousExteriorProduct(n, m);
	-- Rp	== NonNormalizingQuotientBy(R, P);
	Rp	== QuotientBy(R, P, false);
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
	L:LinearOrdinaryDifferentialOperatorCategory0 R, n:I, m:I, P:R): with {
		exteriorPower: L -> L;
		exteriorPower: L -> (R, M R);
		symmetricPower: L -> L;
		symmetricPower: L -> (R, M R);
} == add {
	-- must only code the derivation on power products
	-- case where the leading coeff p of L is not invertible
	-- computes then p times the induced derivation
	local exteriorDerivation(op:L, p:R):(EPP -> EH) == {
		import from Z, Rp, ARR Rp, Partial EPP;
		a:ARR Rp := new m;
		for i in 0..prev m repeat
			a(next i) := - normalize(coefficient(op, i::Z)::Rp);
		pp := shift(1@Rp, 1);
		(y:EPP):EH +-> {
			q:EH := 0;
			for i in 1..n repeat {
				if ~failed?(u := increment(y, i)) then
					q := add!(q, pp, retract u);
			}
			~appears?(y, m) => q;
			for i in 1..m repeat {
				(s, z) := replace(y, m, i);
				if ~zero?(s) then q := add!(q, s::Z * a.i, z);
			}
			q;
		}
	}

	-- must only code the derivation on power products
	-- case where the leading coeff p of L is not invertible
	-- computes then p times the induced derivation
	local inducedDerivation(op:L, p:R):(PP -> H) == {
		import from Z, Rp, ARR Rp;
		a:ARR Rp := new m;
		for i in 0..prev m repeat
			a(next i) := - normalize(coefficient(op, i::Z)::Rp);
		(y:PP):H +-> {
			TRACE("ffsympow::inducedDerivation: y = ", y);
			q:H := 0;
			TRACE("ffsympow::inducedDerivation: q = ", q);
			for i in 1..prev m | (d := degree(y, i)) > 0 repeat {
				c := shift(d::Rp, 1);
				q := add!(q, c, incdec(y, next i, i));
				TRACE("ffsympow::inducedDerivation: q = ", q);
			}
			zero?(d := degree(y, m)) => q;
			e := d::Z;
			for i in 1..m | ~zero?(a.i) repeat {
				q := add!(q, e * a.i, incdec(y, i, m));
				TRACE("ffsympow::inducedDerivation: q = ", q);
			}
			q;
		}
	}

	-- case where the leading coeff p of L is not invertible
	-- uses then p times the induced derivation
	symmetricPower(op:L):(R, M R) == {
		TRACE("ffsympow::symmetricPower: op = ", op);
		START__TIME;
		import from Z, PP;
		p := leadingCoefficient op;
		TRACE("ffsympow::symmetricPower: p = ", p);
		D := inducedDerivation(op, p);
		dim := retract(#$PP);
		TRACE("ffsympow::symmetricPower: dim = ", dim);
		mat := zero(dim, dim);
		for i in 1..dim repeat vectorize!(mat, i, D lookup i);
		TIME("ffsympow::symmetricPower: matrix at ");
		TRACE("ffsympow::symmetricPower: mat = ", mat);
		(p, mat);
	}

	-- case where the leading coeff p of L is not invertible
	-- uses then p times the exterior derivation
	exteriorPower(op:L):(R, M R) == {
		START__TIME;
		import from Z, EPP;
		p := leadingCoefficient op;
		D := exteriorDerivation(op, p);
		dim := retract(#$EPP);
		mat := zero(dim, dim);
		for i in 1..dim repeat vectorize!(mat, i, D lookup i);
		TIME("ffsympow::exteriorPower: matrix at ");
		(p, mat);
	}

	-- case where the leading coeff p of L is not invertible
	-- uses then p times the induced derivation
	symmetricPower(op:L):L == { 
		import from Z, Rp, Derivation R, Derivation Rp, H;
		import from FractionFreeCyclicVector(R, L, P);
		p := leadingCoefficient op;
		D := derivation$L;
		DRp := lift D;
		pD := derivation((x:Rp):Rp +-> shift(DRp x, 1));
		DL := lift(pD, inducedDerivation(op, p));
		firstAnnihilator makeMatrix(D(p)::Rp, DL);
	}

	-- case where the leading coeff p of L is not invertible
	-- uses then p times the exterior derivation
	exteriorPower(op:L):L == { 
		import from Z, Rp, Derivation R, Derivation Rp, EH;
		import from FractionFreeCyclicVector(R, L, P);
		p := leadingCoefficient op;
		D := derivation$L;
		DRp := lift D;
		pD := derivation((x:Rp):Rp +-> shift(DRp x, 1));
		DL := lift(pD, exteriorDerivation(op, p));
		firstAnnihilator makeExtMatrix(D(p)::Rp, DL);
	}

	-- D is already p times the induced derivation
	local makeMatrix(Dp:Rp, D:H -> H):M Rp == {
		import from Z, PP, H;
		nu:Z := 0;
		dim := retract(#$PP);
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
		dim := retract(#$EPP);
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

	local vectorize!(mat:M R, i:I, y:H):() == {
		import from Rp;
		for j in 1..cols mat repeat
			mat(i, j) := numerator coefficient(y, j);
	}

	local vectorize!(mat:M R, i:I, y:EH):() == {
		import from Rp;
		for j in 1..cols mat repeat
			mat(i, j) := numerator coefficient(y, j);
	}

	local vectorize!(mat:M Rp, j:I, y:H):() == {
		dim := rows mat;
		for i in 1..dim repeat mat(dim + 1 - i, j) := coefficient(y, i);
	}

	local vectorize!(mat:M Rp, j:I, y:EH):() == {
		dim := rows mat;
		for i in 1..dim repeat mat(dim + 1 - i, j) := coefficient(y, i);
	}
}
