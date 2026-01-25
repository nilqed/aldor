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
------------------------------ sit_lodocat.as ------------------------------
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I	== MachineInteger;
	Z	== Integer;
	RID	== R pretend IntegralDomain;
	PP	== DenseHomogeneousPowerProduct(n, m);
	SP	== SymmetricPower(RID, %, n, m);
	FFSP	== FactorFreeSymmetricPower(RID, %, n, m, p, irr? p);
	SYMPOW2	== SecondOrderSymmetricPower(RID, %);
}

-- This category is documented in sit_lodoct0.as
define LinearOrdinaryDifferentialOperatorCategory(R:Ring):
  Category == LinearOrdinaryDifferentialOperatorCategory0 R with {
	default {
		if R has IntegralDomain then {
			local decomp?:Boolean == R has DecomposableRing;

			exteriorPower(L:%, N:Z):% == {
				import from I, R;
				assert(N > 0);
				zero? L or one?(n := machine N) => L;
				m := machine(d := degree L);
				n > m => 1;
				a := leadingCoefficient L;
				n = m => {
					b := coefficient(L, prev d);
					zero? b => monom;
					monomial(a, 1) + b::%;
				}
				extpow(L, n, m, a);
			}

			symmetricPower(L:%, N:Z):% == {
				import from I;
				assert(N > 0);
				zero? L or one?(n := machine N)
					or zero?(m := machine degree L) => L;
				m = 2 => symmetricPower(L, N)$SYMPOW2;
				sympow(L, n, m, leadingCoefficient L);
			}

			local irr?(p:R):Boolean == {
				macro RD == (R pretend DecomposableRing);
				decomp? => provablyIrreducible?(p)$RD;
				false;
			}

			-- creating a new scope is necessary
			local sympow(L:%, n:I, m:I, p:R):% == {
				import from Partial R;
				failed?(u := reciprocal p) =>
							symmetricPower(L)$FFSP;
				symmetricPower(L, retract u)$SP;
			}

			-- creating a new scope is necessary
			local extpow(L:%, n:I, m:I, p:R):% == {
				import from Partial R;
				failed?(u := reciprocal p) =>
							exteriorPower(L)$FFSP;
				exteriorPower(L, retract u)$SP;
			}
		}
	}
}
