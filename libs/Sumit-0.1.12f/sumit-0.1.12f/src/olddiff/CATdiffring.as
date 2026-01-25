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
------------------------------ CATdiffring.as ----------------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1994

#include "sumit"

#if ASDOC
\thistype{DifferentialRing}
\History{Manuel Bronstein}{21/12/94}{created}
\Usage{\this: Category}
\Descr{\this~is the category of \sumit commutative differential rings.}
\begin{exports}
\category{CommutativeRing}\\
derivation: & $\to$ Derivation \% & The derivation\\
differentiate: & (\%, Integer) $\to$ \% & Differentiate an element\\
\end{exports}
#endif

DifferentialRing: Category == CommutativeRing with {
	-- TEMPORARY: NO CONDITIONAL CONSTANTS (969)
	--derivation: Derivation %;
	derivation: () -> Derivation %;
#if ASDOC
\aspage{derivation}
\Usage{\name}
\Signature{}{Derivation \%}
\Retval{Returns the derivation of the ring.}
\seealso{differentiate(\this)}
#endif
	differentiate: % -> %;
	differentiate: (%, Integer) -> %;
#if ASDOC
\aspage{differentiate}
\Usage{\name~x\\\name(x, n)}
\Signature{(\%, Integer)}{\%}
\Params{
{\em x} & \% & The element to differentiate\\
{\em n} & Integer & The order of differentiation (optional)\\
}
\Retval{
\name~x returns $x'$, the derivative of $x$.\\
\name(x, n) returns $x^{(n)}$, the \Th{n} derivative of $x$.
}
\seealso{derivation(\this)}
#endif
	default {
		-- TEMPORARY: NO CONDITIONAL CONSTANTS (969)
		-- derivation:Derivation % ==
		derivation():Derivation % ==
			derivation((r:%):% +-> differentiate r);

		differentiate(x:%, n:Integer):% == {
			import from Derivation %;
			ASSERT(n >= 0);
			-- TEMPORARY: NO CONDITIONAL CONSTANTS (969)
			-- derivation(x, n);
			derivation()(x, n);
		}
	}
}

