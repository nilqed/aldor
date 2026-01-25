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
-- Copyright (c) Manuel Bronstein 2000-2001
-- Copyright (c) INRIA 2000-2001, Version 0.1.13
-- Logiciel Shasta (c) INRIA 2000-2001, dans sa version 0.1.13
-----------------------------------------------------------------------------

#include "sumit"

#library lib1	"multlodo.ao"
import from lib1;
inline from lib1;

macro {
	Z == Integer;
	R == MultiLodo(ZX, QX, Qxd);
}

LODOEvaluator(ZX:UnivariatePolynomialCategory Z,
	QX:UnivariatePolynomialCategory Fraction Z,
	Qxd:LinearOrdinaryRecurrenceCategory Fraction QX): Evaluator R == add {
		import from String;

		local sadjoint:Symbol		== -"adjoint";
		local sapply:Symbol		== -"apply";
		local scoefficient:Symbol	== -"coefficient";
		local sdecompose:Symbol		== -"decompose";
		local sdegree:Symbol		== -"degree";
		local sdispersion:Symbol	== -"dispersion";
		local seigenring:Symbol		== -"eigenring";
		local selement:Symbol		== -"element";
		local sexteriorPower:Symbol	== -"exteriorPower";
		local sfactor:Symbol		== -"factor";
		local shyper:Symbol		== -"hyper";
		local skernel:Symbol		== -"kernel";
		local sleftGcd:Symbol		== -"leftGcd";
		local sleftLcm:Symbol		== -"leftLcm";
		local sliouvillian:Symbol	== -"liouvillianSolution";
		local sLoewy:Symbol		== -"Loewy";
		local smakeIntegral:Symbol	== -"makeIntegral";
		local snormalize:Symbol		== -"normalize";
		local spolynomial:Symbol	== -"polynomialSolution";
		local srational:Symbol		== -"rationalSolution";
		local srightGcd:Symbol		== -"rightGcd";
		local srightLcm:Symbol		== -"rightLcm";
		local ssections:Symbol		== -"sections";
		local sshift:Symbol		== -"shift";
		local sspread:Symbol		== -"spread";
		local ssystem:Symbol		== -"system";

		evalPrefix!(name:Symbol, nargs:MachineInteger,
			args:List R, tab:SymbolTable R):Partial R == {
				nargs = 1 => eval1(name, first args);
				nargs = 2 => eval2(name, first args,
							first rest args);
				name = ssystem => system(nargs, args)$R;
				failed;
		}

		local eval1(name:Symbol, x:R):Partial R == {
			name = sadjoint => adjoint x;
			name = sdecompose => decompose x;
			name = sdegree => degree x;
			name = sdispersion => dispersion x;
			name = seigenring => eigenring x;
			name = sfactor => factor x;
			name = shyper => hyper x;
			name = skernel => kernel x;
			name = sliouvillian => liouvillianSolution x;
			name = sLoewy => Loewy x;
			name = smakeIntegral => makeIntegral x;
			name = snormalize => normalize x;
			name = sshift => shift(x, 1);
			name = sspread => spread x;
			name = ssystem => system x;
			failed;
		}

		local eval2(name:Symbol, x:R, y:R):Partial R == {
			name = sapply => x y;
			name = scoefficient => coefficient(x, y);
			name = sdispersion => dispersion(x, y);
			name = selement => element(x, y);
			name = sexteriorPower => exteriorPower(x, y);
			name = sleftGcd => leftGcd(x, y);
			name = sleftLcm => leftLcm(x, y);
			name = spolynomial => polynomialSolution(x,y);
			name = srational => rationalSolution(x, y);
			name = srightGcd => rightGcd(x, y);
			name = srightLcm => rightLcm(x, y);
			name = ssections => sections(x, y);
			name = sshift => shift(x, y);
			name = sspread => spread(x, y);
			failed;
		}
}
