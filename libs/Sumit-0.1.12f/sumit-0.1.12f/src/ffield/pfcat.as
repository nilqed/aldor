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
----------------------------- pfcat.as ----------------------------------
#include "sumit"

#if ASDOC
\thistype{PrimeFieldCategory}
\History{Manuel Bronstein}{24/7/98}{created}
\Usage{\this: Category}
\Descr{\this~is the category for prime fields of the form $\ZZ / p \ZZ$.}
\begin{exports}
\category{PrimeFieldCategory0}\\
\category{FactorizationRing}\\
roots: &
(P:UnivariatePolynomialCategory0 \%) $\to$ P $\to$ List Cross(\%, Integer) &
In-field roots\\
\end{exports}
#endif

macro {
	Z == Integer;
	RR == RationalRoot;
	POLY == UnivariatePolynomialCategory0;
}

PrimeFieldCategory:Category == Join(PrimeFieldCategory0,FactorizationRing) with{
	roots: (P:POLY %) -> P -> List Cross(%, Z);
	rootsSqfr: (P:POLY %) -> P -> List %;
	default {
		local ratroot(r:%, e:Z):RR == integerRoot(biglift r, e);

		rationalRoots(P:POLY %):P -> List RR == integerRoots P;

		roots(P:POLY %):P -> List Cross(%, Z) == {
			import from PrimeFieldUnivariateFactorizer(%, P);
			(p:P):List Cross(%, Z) +-> roots p;
		}

		rootsSqfr(P:POLY %):P -> List % == {
			import from PrimeFieldUnivariateFactorizer(%, P);
			(p:P):List % +-> rootsSqfr p;
		}

		integerRoots(P:POLY %):P -> List RR == {
			import from List Cross(%, Z);
			rootP := roots P;
			(p:P):List RR +-> [ratroot r for r in rootP p];
		}

		factor(P:POLY %):P -> (%, Product P) == {
			import from PrimeFieldUnivariateFactorizer(%, P);
			(p:P):(%, Product P) +-> factor p;
		}
	}
}
