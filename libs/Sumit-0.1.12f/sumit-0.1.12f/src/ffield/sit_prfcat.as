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
---------------------------- sit_prfcat.as --------------------------------
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{PrimeFieldCategory}
\History{Manuel Bronstein}{24/7/98}{created}
\Usage{\this: Category}
\Descr{\this~is the category for prime fields,\ie fields of the form
$\ZZ / p \ZZ$ where $p \in \ZZ$ is a prime.}
\begin{exports}
\category{\astype{PrimeFieldCategory0}}\\
\category{\astype{FactorizationRing}}\\
\asexp{roots}:
&(P:POLY \%) $\to$ P $\to$ \astype{List} \builtin{Cross}(\%, \astype{Integer})&
In--field roots\\
\asexp{rootsSqfr}:
& (P:POLY \%) $\to$ P $\to$ \astype{List} \% & In--field roots\\
\end{exports}
\begin{aswhere}
POLY &==& \astype{UnivariatePolynomialCategory0}\\
\end{aswhere}
#endif

macro {
	Z == Integer;
	FR == FractionalRoot;
	RR == FractionalRoot Z;
	POLY == UnivariatePolynomialCategory0;
}

define PrimeFieldCategory:Category ==
	Join(PrimeFieldCategory0, FactorizationRing) with{
		rootsSqfr: (P:POLY %) -> P -> Generator %;
#if ALDOC
\aspage{rootsSqfr}
\Usage{\name~P\\ \name(P)(p)}
\Signature{(P:\astype{UnivariatePolynomialCategory0} \%)}
{P $\to$ \astype{Generator} \%}
\Params{
{\em P} & \astype{UnivariatePolynomialCategory0} \% & a polynomial type\\
{\em p} & P & a squarefree polynomial\\
}
\Retval{Returns a generator that produces all the roots of $p$, which
must be squarefree, in its coefficient field.}
#endif
	default {
		rationalRoots(P:POLY %):P -> Generator RR == integerRoots P;

		local ratroot(r:FR %):RR ==
			integralRoot(lift integralValue r, multiplicity r);

		roots(P:POLY %):P -> Generator FR % == {
			import from Boolean,PrimeFieldUnivariateFactorizer(%,P);
			(p:P):Generator FR % +-> roots(p, false);
		}

		rootsSqfr(P:POLY %):P -> Generator % == {
			import from Boolean, FR %;
			import from PrimeFieldUnivariateFactorizer(%, P);
			(p:P):Generator % +-> generate {
				for r in roots(p, true) repeat
					yield integralValue r;
			}
		}

		integerRoots(P:POLY %):P -> Generator RR == {
			rootP := roots P;
			(p:P):Generator RR +-> generate {
				for r in rootP p repeat yield ratroot r;
			}
		}

		factor(P:POLY %):P -> (%, Product P) == {
			import from PrimeFieldUnivariateFactorizer(%, P);
			(p:P):(%, Product P) +-> factor p;
		}
	}
}
