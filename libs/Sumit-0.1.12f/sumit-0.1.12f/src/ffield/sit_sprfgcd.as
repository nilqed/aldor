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
--------------------------- sit_sprfgcd.as ------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it ©INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I == MachineInteger;
	Z == Integer;
	A == PrimitiveArray;
}

SmallPrimeFieldCategoryGcd(F:SmallPrimeFieldCategory0,
				FX:UnivariatePolynomialCategory0 F): with {
	gcdSPF: (FX, FX) -> FX;
	gcdquoSPF: (FX, FX) -> (FX, FX, FX);
} == add {
	local charac:Z	== characteristic$F;
	-- TEMPORARY: TERRIBLE 1.1.11e/12 COMPILER BUG (1181?)
	-- local schar:I	== machine charac;

	local array(p:FX, d:I):A I == {
		import from Z, F;
		a := new(next d, 0);
		for term in p repeat {
			(c, e) := term;
			a(d - machine e) := machine c;
		}
		a;
	}

	gcdSPF(p:FX, q:FX):FX == {
		import from I, A I, Z, F, ModulopUnivariateGcd;
		zero? p => monic q;
		zero? q => monic p;
		zero?(dp := degree p) or zero?(dq := degree q) => 1;
		-- TEMPORARY: TERRIBLE 1.1.11e/12 COMPILER BUG (1181?)
		if dp < dq then {	-- swap p,q
			ap := array(q, ep := machine dq);
			aq := array(p, eq := machine dp);
		}
		else {
			ap := array(p, ep := machine dp);
			aq := array(q, eq := machine dq);
		}
		assert(ep >= eq);
		schar:I := machine charac;
		(log, exp, log?) := discreteLogTable$F;
		(v, d, s) := {
			log? => gcd!(ap, ep, aq, eq, 1, schar, log, exp);
			gcd!(ap, ep, aq, eq, 1, schar);
		}
		-- monic gcd is now in v(s),v(s+1),...
		g:FX := 0;
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 0..d repeat g := add!(g, v(s+i)::F, (d-i)::Z);
		i:I := 0; while i <= d repeat {
			g := add!(g, v(s+i)::F, (d-i)::Z);
			i := next i;
		}
		g;
	}

	gcdquoSPF(p:FX, q:FX):(FX, FX, FX) == {
		g := gcdSPF(p, q);
		(g, quotient(p, g), quotient(q, g));
	}
}
