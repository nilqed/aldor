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
------------------------------ CATdiffext.as ----------------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1994

#include "sumit"

#if ASDOC
\thistype{DifferentialExtension}
\History{Manuel Bronstein}{22/12/94}{created}
\Usage{\this~R: Category}
\Params{ {\em R} & CommutativeRing & The base ring\\ }
\Descr{\this(R)~is the category of differential extensions of R.}
\begin{exports}
\category{CommutativeRing}\\
lift: & Derivation R $\to$ Derivation \% & Extension of a derivation\\
\end{exports}
\begin{exports}[if R has DifferentialRing then]
\category{DifferentialRing}\\
\end{exports}
#endif

DifferentialExtension(R:CommutativeRing):
	Category == CommutativeRing with {
	lift: Derivation R -> Derivation %;
#if ASDOC
\aspage{lift}
\Usage{\name~D}
\Signature{Derivation R}{Derivation \%}
\Params{ {\em D} & Derivation R & A derivation on R\\ }
\Retval{Returns the derivation $D$ extended to the ring extension.}
#endif
	if R has DifferentialRing then DifferentialRing;
	default {
		if R has DifferentialRing then {
			differentiate(x:%):% == {
				import from Derivation %;
				-- TEMPORARY: NO CONDITIONAL CONSTANTS (969)
				-- lift(derivation$R) x;
				lift(derivation()$R) x;
			}
		}
	}
}

