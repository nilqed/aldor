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
----------------------------- sit_diffext.as ----------------------------------
--
-- Differential extensions
--
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{DifferentialExtension}
\History{Manuel Bronstein}{22/12/94}{created}
\Usage{\this~R: Category}
\Params{ {\em R} & \astype{CommutativeRing} & The base ring\\ }
\Descr{\this(R)~is the category of differential extensions of R.}
\begin{exports}
\category{\astype{CommutativeRing}}\\
\asexp{lift}: & \astype{Derivation} R $\to$ \astype{Derivation} \% &
Extension of a derivation\\
\end{exports}
\begin{exports}[if R has \astype{DifferentialRing} then]
\category{\astype{DifferentialRing}}\\
\end{exports}
#endif

define DifferentialExtension(R:CommutativeRing):Category==CommutativeRing with {
	lift: Derivation R -> Derivation %;
#if ALDOC
\aspage{lift}
\Usage{\name~D}
\Signature{\astype{Derivation} R}{\astype{Derivation} \%}
\Params{ {\em D} & \astype{Derivation} R & A derivation on R\\ }
\Retval{Returns the derivation $D$ extended to the ring extension.}
#endif
	if R has DifferentialRing then DifferentialRing;
	default {
		if R has DifferentialRing then {
			differentiate(x:%):% == {
				import from Derivation %;
				lift(derivation$R) x;
			}
		}
	}
}

