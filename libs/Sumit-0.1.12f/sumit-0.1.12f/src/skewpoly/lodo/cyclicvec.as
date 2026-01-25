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
------------------------------ cyclicvec.as ------------------------------
#include "sumit"

macro {
	I	== SingleInteger;
	Z	== Integer;
	V	== Vector;
	M	== DenseMatrix;
	LA	== LinearAlgebra;
	OGE	== OrdinaryGaussElimination(R pretend SumitField, M R);
	FFGE	== TwoStepFractionFreeGaussElimination;
	-- FFGE	== FractionFreeGaussElimination;
	REC	== Record(list: List V R);
}

CyclicVector(R:IntegralDomain,
	L:LinearOrdinaryDifferentialOperatorCategory0 R,
	T:BasicType): with {
		firstAnnihilator: (T -> T, T -> V R, T) -> (L, List V R);
} == add {
	local field?:Boolean == R has SumitField;

	-- returns (a_0 + a_1 D + ... + a_n D^n, [v_n, v_{n-1}, ..., v_0])
	-- such that v_i = vec(f^i(y)) and a_0 v_0 + ... + a_n v_n = 0
	-- and there is no shorter dependence
	firstAnnihilator(f:T -> T, vec:T -> V R, y:T):(L, List V R) == {
		import from I, Z, V R, List V R, REC;
		dim := #(vec y);
		rec:REC := [empty()];
		mindep := depend(cyclicGenerator!(f, y, vec, rec), dim);
		Ln:L := 0;
		for i in 1..#mindep repeat
			Ln:= add!(Ln, mindep.i, (prev i)::Z);
		(Ln, rec.list);
	}

	local depend(g:Generator V R, dim:I):V R == {
		field? => firstDependence(g, dim)$LA(R, M R, OGE);
		firstDependence(g, dim)$LA(R, M R, FFGE(R, M R));
	}

	-- cons'es each vector generated to rec.list
	local cyclicGenerator!(f:T->T,y:T,vec:T->V R,rec:REC):Generator V R ==
		generate {
			repeat {
				rec.list := cons(v := vec y, rec.list);
				yield v;
				y := f y;
			}
	}
}
