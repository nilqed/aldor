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
--------------------------- gcdint.as -------------------------------------
#include "sumit"

extend Integer: UnivariateGcdRing == add {
	gcdquoUP(P:UnivariatePolynomialCategory0 %):(P,P)->(P,P,P) == {
		(p:P, q:P):(P, P, P) +-> {
			import from Partial P;
			import from HeuristicGcd(%,P),ModularUnivariateGcd(%,P);
			(g, y, z) := modularGcd(p, q);
#if REPORTFAILURE
			if failed? g then reportFailure(P, p, q);
#endif
			if failed? g then (g, y, z) := heuristicGcd(p, q);
			failed? g => {
				import from Resultant(%, P);
				srg := subResultantGcd(p, q);
				(srg, quotient(p, srg), quotient(q, srg));
			}
			(retract g, y, z);
		}
	}

	gcdUP(P:UnivariatePolynomialCategory0 %):(P,P)->P == {
		(p:P, q:P):P +-> {
			-- TEMPORARY: COMPILER SEES 2 MEANINGS FOR gcdquoUP !
			-- (g, y, z) := gcdquoUP(P)(p, q);
			-- g;
			import from Partial P;
			import from HeuristicGcd(%,P),ModularUnivariateGcd(%,P);
			(g, y, z) := modularGcd(p, q);
#if REPORTFAILURE
			if failed? g then reportFailure(P, p, q);
#endif
			if failed? g then (g, y, z) := heuristicGcd(p, q);
			failed? g => {
				import from Resultant(%, P);
				subResultantGcd(p, q);
			}
			retract g;
		}
	}

#if REPORTFAILURE
	reportFailure(P:UnivariatePolynomialCategory0 %, p:P, q:P):() == {
		import from TextWriter, OperatingSystemInterface, FileName;
		import from String, ExpressionTree, OutFile;
		tmp := filename(tmpDirName(), "modgcd", "sit");
		ntmp := unparse tmp;
		ftmp := open tmp;
		error << "ModularGCD failure - reported to asharp@inf.ethz.ch";
		error << newline;
		wtmp := writer ftmp;
		wtmp << "ModularGCD failed on:" << newline;
		maple(wtmp, extree p);
		wtmp << newline << "and" << newline;
		maple(wtmp, extree q);
		wtmp << newline;
		close ftmp;
		run concat("mail asharp@inf.ethz.ch < ", ntmp);
		fileRemove ntmp;
	}
#endif
}

