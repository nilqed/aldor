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
----------------------------- sit_fring.as --------------------------------
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	Z == Integer;
	FR == FractionalRoot;
	POL == UnivariatePolynomialCategory0;
}

#if ALDOC
\thistype{FactorizationRing}
\History{Manuel Bronstein}{27/4/98}{created}
\Usage{\this: Category}
\Descr{\this~is the category of rings that export an algorithm for
factoring univariate polynomials over themselves into irreducibles.}
\begin{exports}
\category{\astype{GcdDomain}}\\
\category{\astype{RationalRootRing}}\\
\asexp{factor}:
& (P:POL \%) $\to$ P $\to$ (\%, Product P) & Factorization into irreducibles\\
\asexp{fractionalRoots}:
& (P:POL \%) $\to$ P $\to$ \astype{Generator} FR \% &
Roots in the fraction field\\
\asexp{roots}:
& (P:POL \%) $\to$ P $\to$ \astype{Generator} FR \% &
Roots in the coefficient ring\\
\end{exports}
\begin{aswhere}
FR &==& \astype{FractionalRoot}\\
POL &==& \astype{UnivariatePolynomialCategory0}\\
\end{aswhere}
#endif

define FactorizationRing:Category== Join(GcdDomain, RationalRootRing) with {
	factor: (P:POL %) -> P -> (%, Product P);
#if ALDOC
\aspage{factor}
\Usage{ \name(P)(p) }
\Signature
{(P: \astype{UnivariatePolynomialCategory0} \%)}
{P $\to$ (\%, \astype{Product} P)}
\Params{
{\em P} & \astype{UnivariatePolynomialCategory0} \% & A polynomial type\\
{\em p} & P & A polynomial\\
}
\Retval{Returns $(c, p_1^{e_1} \cdots p_n^{e_n})$ such that
each $p_i$ is irreducible, the $p_i$'s have no common factors, and
$$
p = c\;\prod_{i=1}^n p_i^{e_i}\,.
$$
}
#endif
	fractionalRoots: (P:POL %) -> P -> Generator FR %;
	roots: (P:POL %) -> P -> Generator FR %;
#if ALDOC
\aspage{fractionalRoots,roots}
\astarget{fractionalRoots}
\astarget{roots}
\Usage{ fractionalRoots(P)(p)\\ roots(P)(p) }
\Signature{(P: POL \%)}{P $\to$ \astype{Generator} \builtin{FractionalRoot} \%}
\begin{aswhere}
POL &==& \astype{UnivariatePolynomialCategory0}\\
\end{aswhere}
\Params{
{\em P} & \astype{UnivariatePolynomialCategory0} \% & A polynomial type\\
{\em p} & P & A polynomial\\
}
\Retval{Returns a generator that produces all the roots $p$
either in the ring or in its fraction field.}
#endif
	default {
		roots(P:POL %):P -> Generator FR % == {
			froots := fractionalRoots P;
			(p:P):Generator FR % +-> generate {
				import from FR %;
				for z in froots p | integral? z repeat yield z;
			}
		}

		fractionalRoots(P:POL %):P -> Generator FR % == {
			fact := factor P;
			(p:P):Generator FR % +-> generate {
				import from Z, FR %, Product P;
				(c, fp) := fact p;
				for term in fp repeat {
					(q, n) := term;
					if one? degree q then {
						num := - coefficient(q, 0);
						den := leadingCoefficient q;
						yield fractionalRoot(num,den,n);
					}
				}
			}
		}
	}
}

