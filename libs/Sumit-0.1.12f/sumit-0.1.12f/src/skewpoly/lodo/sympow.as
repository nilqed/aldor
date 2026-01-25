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
------------------------------ sympow.as ------------------------------
#include "sumit"

macro {
	I	== SingleInteger;
	Z	== Integer;
	V	== Vector;
	M	== DenseMatrix;
	ARR	== PrimitiveArray;
	PP      == DenseHomogeneousPowerProduct(n, m);
	H       == DenseHomogeneousPolynomial(R, n, m);
	EPP	== DenseHomogeneousExteriorProduct(n, m);
	EH	== DenseHomogeneousExteriorPower(R, n, m);

}

-- m = order of the operator
-- n = symmetric power to compute
-- This code should not be used for 2nd order operators, for which
--   SecondOrderSymmetricPower is more appropriate
SymmetricPower(R:IntegralDomain,
	L:LinearOrdinaryDifferentialOperatorCategory0 R, n:I, m:I): with {
		exteriorPower: (L, R) -> L;
		exteriorPower: (L, R) -> M R;
		symmetricPower: (L, R) -> L;
		symmetricPower: (L, R) -> M R;
} == add {
	local field?:Boolean == R has SumitField;

	-- must only code the derivation on power products
	-- case where the leading coeff of L is invertible
	-- ainv = inverse of leading coeff
	-- can then perform the calculations in R
	local exteriorDerivation(op:L, ainv:R):(EPP -> EH) == {
		import from Z, ARR R, Partial EPP;
		a:ARR R := new m;
		for i in 0..prev m repeat
			a(next i) := - ainv * coefficient(op, i::Z);
		(y:EPP):EH +-> {
			q:EH := 0;
			for i in 1..n repeat {
				if ~failed?(u := increment(y, i)) then
					q := add!(q, 1, retract u);
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
	-- case where the leading coeff of L is invertible
	-- ainv = inverse of leading coeff
	-- can then perform the calculations in R
	local inducedDerivation(op:L, ainv:R):(PP -> H) == {
		import from Z, ARR R;
		a:ARR R := new m;
		for i in 0..prev m repeat
			a(next i) := - ainv * coefficient(op, i::Z);
		(y:PP):H +-> {
			q:H := 0;
			for i in 1..prev m | (d := degree(y, i)) > 0 repeat
				q := add!(q, d::R, incdec(y, next i, i));
			zero?(d := degree(y, m)) => q;
			e := d::Z;
			for i in 1..m repeat
				q := add!(q, e * a.i, incdec(y, i, m));
			q;
		}
	}

	-- case where the leading coeff of L is invertible
	-- ainv = inverse of leading coeff
	-- can then perform the calculations in R
	symmetricPower(op:L, ainv:R):M R == {
		START__TIME;
		import from Z, PP;
		dim := retract(#$PP);
		mat:M R := zero(dim, dim);
		D := inducedDerivation(op, ainv);
		for i in 1..dim repeat vectorize!(mat, i, D lookup i);
		TIME("sympow::symmetricPower: matrix at ");
		mat;
	}

	-- case where the leading coeff of L is invertible
	-- ainv = inverse of leading coeff
	-- can then perform the calculations in R
	exteriorPower(op:L, ainv:R):M R == {
		START__TIME;
		import from Z, EPP;
		dim := retract(#$EPP);
		mat:M R := zero(dim, dim);
		D := exteriorDerivation(op, ainv);
		for i in 1..dim repeat vectorize!(mat, i, D lookup i);
		TIME("sympow::exteriorPower: matrix at ");
		mat;
	}

	-- case where the leading coeff of L is invertible
	-- ainv = inverse of leading coeff
	-- can then perform the calculations in R
	symmetricPower(op:L, ainv:R):L == {
		import from Z, PP, H, V R, CyclicVector(R, L, H);
		DL := lift(derivation, inducedDerivation(op, ainv));
		y := monomial(1, monomial 1);
		v:V R := zero retract(#$PP);
		(sympow, l) := firstAnnihilator(DL, vectorize! v, y);
		sympow;
	}

	-- case where the leading coeff of L is invertible
	-- ainv = inverse of leading coeff
	-- can then perform the calculations in R
	exteriorPower(op:L, ainv:R):L == {
		import from Z, EPP, EH, V R, CyclicVector(R, L, EH);
		DL := lift(derivation, exteriorDerivation(op, ainv));
		y := monomial(1, principalProduct);
		v:V R := zero retract(#$EPP);
		(extpow, l) := firstAnnihilator(DL, vectorize! v, y);
		extpow;
	}

	local vectorize!(mat:M R, i:I, y:EH):() == {
		for j in 1..cols mat repeat mat(i, j) := coefficient(y, j);
	}

	local vectorize!(mat:M R, i:I, y:H):() == {
		for j in 1..cols mat repeat mat(i, j) := coefficient(y, j);
	}

	local vectorize!(v:V R)(y:H):V R == {
		for i in 1..#v repeat v.i := coefficient(y, i);
		v;
	}

	local vectorize!(v:V R)(y:EH):V R == {
		for i in 1..#v repeat v.i := coefficient(y, i);
		v;
	}
}
