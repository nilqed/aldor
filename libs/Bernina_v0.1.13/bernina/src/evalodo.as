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
------------------------ evalodo.as ------------------------------
--
-- Copyright (c) Manuel Bronstein 1994-2001
-- Copyright (c) INRIA 1997-2001, Version 0.1.13
-- Logiciel Bernina (c) INRIA 1997-2001, dans sa version 0.1.13
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-1997
-----------------------------------------------------------------------------

#include "sumit"

#library lib1	"multlodo.ao"
import from lib1;
inline from lib1;

macro {
	Z == Integer;
	R == MultiLodo(ZX, QX, Qxd, Qxy);
}

LODOEvaluator(ZX:UnivariatePolynomialCategory Z,
	QX:UnivariatePolynomialCategory Fraction Z,
	Qxd:LinearOrdinaryDifferentialOperatorCategory Fraction QX,
	Qxy:UnivariatePolynomialCategory Fraction QX):
	Evaluator R == add {
		import from String;

		local sadjoint:Symbol		== -"adjoint";
		local sall:Symbol		== -"allRationalExponents";
		local sapply:Symbol		== -"apply";
		local scoefficient:Symbol	== -"coefficient";
		local sDarboux:Symbol		== -"Darboux";
		local sdecompose:Symbol		== -"decompose";
		local sdegree:Symbol		== -"degree";
		local sdiff:Symbol		== -"diff";
		local sdual:Symbol		== -"dualFirstIntegral";
		local seigenring:Symbol		== -"eigenring";
		local selement:Symbol		== -"element";
		local sexpSolutions:Symbol	== -"exponentialSolutions";
		local sexteriorKernel:Symbol	== -"exteriorKernel";
		local sexteriorPower:Symbol	== -"exteriorPower";
		local sextPower:Symbol		== -"extPower";
		local sfactor:Symbol		== -"factor";
		local sinvariants:Symbol	== -"invariants";
		local skernel:Symbol		== -"kernel";
		local sleftGcd:Symbol		== -"leftGcd";
		local sleftLcm:Symbol		== -"leftLcm";
		local sLoewy:Symbol		== -"Loewy";
		local smakeIntegral:Symbol	== -"makeIntegral";
		local snormalize:Symbol		== -"normalize";
		local spcurvature:Symbol	== -"pCurvature";
		local spolynomialSolution:Symbol== -"polynomialSolution";
		local sradiinv:Symbol		== -"radicalInvariants";
		local sradicalSolutions:Symbol	== -"radicalSolutions";
		local srationalSolution:Symbol	== -"rationalSolution";
		local srightGcd:Symbol		== -"rightGcd";
		local srightLcm:Symbol		== -"rightLcm";
		local ssemiinv:Symbol		== -"semiInvariants";
		local ssolve2:Symbol		== -"solve2";
		local ssymmetricKernel:Symbol	== -"symmetricKernel";
		local ssymmetricPower:Symbol	== -"symmetricPower";
		local ssymmetricSqrt:Symbol	== -"symmetricSquareRoot";
		local ssymPower:Symbol		== -"symPower";
		local ssystem:Symbol		== -"system";
		local sirr3:Symbol		== -"irreducible3";

		evalPrefix!(name:Symbol, nargs:MachineInteger,
			args:List R, tab:SymbolTable R):Partial R == {
				TRACE("bernina::evalPrefix!, name = ", name);
				-- name = -"parametricKernel" =>
					-- parametricKernel(first args, rest args);
				nargs = 1 => eval1(name, first args);
				nargs = 2 => eval2(name, first args,
							first rest args);
				nargs = 3 => eval3(name, first args,
							first rest args,
							first rest rest args);
				-- name = -"kernel" =>kernel0(first args,rest args);
				-- name = -"kernel" =>kernel0(first args,rest args);
				name = ssystem => system(nargs, args)$R;
				failed;
		}

		-- local kernel0(sys:R, args:List R):Partial R == {
			-- l := reverse args;
			-- kernel(sys, reverse rest l, first l);
		-- }

		local eval1(name:Symbol, x:R):Partial R == {
			name = sadjoint => adjoint x;
			name = sall => allRationalExponents? x;
			name = sDarboux => Darboux x;
			name = sdegree => degree x;
			name = sdiff => D(x, 1);
			name = sdecompose => decompose x;
			name = seigenring => eigenring x;
			name = sexpSolutions => exponentialSolutions x;
			name = sfactor => factor x;
			name = skernel => kernel x;
			name = sLoewy => Loewy x;
			name = smakeIntegral => makeIntegral x;
			name = snormalize => normalize x;
			name = sradicalSolutions => radicalSolutions(x, 0);
			name = ssolve2 => solve2 x;
			name = ssymmetricSqrt => symmetricSquareRoot x;
			name = ssystem => system x;
			failed;
		}

		local eval2(name:Symbol, x:R, y:R):Partial R == {
			name = sapply => x y;
			name = scoefficient => coefficient(x, y);
			name = sdiff => D(x, y);
			name = sdual => dualFirstIntegral(x, y);
			name = seigenring => eigenring(x, y);
			name = selement => element(x, y);
			name = sexteriorKernel => exteriorKernel(x, y);
			name = sexteriorPower => exteriorPower(x, y);
			name = sextPower => extPower(x, y);
			name = sinvariants => invariants(x, y);
			name = sirr3 => irreducible3(x, y);
			name = skernel => kernel(x, y);
			name = sleftGcd => leftGcd(x, y);
			name = sleftLcm => leftLcm(x, y);
			name = spcurvature => pCurvature(x, y);
			name = spolynomialSolution => polynomialSolution(x, y);
			name = sradiinv => radicalInvariants(x, y);
			name = sradicalSolutions => radicalSolutions(x, y);
			name = srationalSolution => rationalSolution(x, y);
			name = srightGcd => rightGcd(x, y);
			name = srightLcm => rightLcm(x, y);
			name = ssemiinv => semiInvariants(x, y);
			name = ssymmetricKernel => symmetricKernel(x, y);
			name = ssymmetricPower => symmetricPower(x, y);
			name = ssymPower => symPower(x, y);
			failed;
		}

		local eval3(name:Symbol, x:R, y:R, z:R):Partial R == {
			name = sradiinv => radicalInvariants(x, y, z);
			failed;
		}
}
