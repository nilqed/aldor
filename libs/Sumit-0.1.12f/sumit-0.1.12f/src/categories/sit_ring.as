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
------------------------------- sit_ring.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{Ring}
\History{Manuel Bronstein}{21/11/94}{created}
\Usage{\this: Category}
\Descr{ \this~is the category of rings, not necessarily commutative.}
\begin{exports}
\category{\astype{AbelianGroup}}\\
\category{\astype{ArithmeticType}}\\
\category{\astype{Monoid}}\\
\asexp{characteristic}: & \astype{Integer} & characteristic\\
\asexp{coerce}: & \astype{Integer} $\to$ \% & embedding of the integers\\
\asexp{factorial}:
& (\%, \%, \astype{MachineInteger}) $\to$ \% & Generalized factorial\\
\asexp{random}: & () $\to$ \% & Get a random element\\
\end{exports}
#endif

define Ring: Category == Join(AbelianGroup, ArithmeticType, Monoid) with {
	characteristic: Integer;
#if ALDOC
\aspage{characteristic}
\Usage{\name}
\Signature{}{\astype{Integer}}
\Retval{Returns the characteristic of the ring.}
#endif
	coerce: Integer -> %;
#if ALDOC
\aspage{coerce}
\Usage{\name~n\\n::\%}
\Signature{\astype{Integer}}{\%}
\Params{ {\em n} & \astype{Integer} & an integer }
\Retval{Returns $n$ seen as an element of the ring.}
#endif
	factorial: (%, %, MachineInteger) -> %;
#if ALDOC
\aspage{factorial}
\Usage{\name(a, s, n)}
\Signature{(\%, \%, \astype{MachineInteger})}{\%}
\Params{
{\em a, s} & \% & Elements of the ring\\
{\em n} & \astype{MachineInteger} & A nonnegative integer\\
}
\Retval{Returns the generalized factorial $\prod_{i=0}^{n-1} (a + i s)$.}
#endif
	random: () -> %;
#if ALDOC
\aspage{random}
\Usage{\name()}
\Signature{()}{\%}
\Retval{Returns a random element.}
#endif
	default {
		(x:%)^(n:MachineInteger):%	== x^(n::Integer);
		(n:Integer) * (x:%):%		== n::% * x;
		random():% == { import from Integer; random()$Integer :: % }

		factorial(a:%, s:%, n:MachineInteger):% == {
			assert(n >= 0);
			zero? n => 1;
			one? n => a;
			zero? a => 0;
			zero? s => a^n;
			b := a;
			for i in 2..n repeat {
				a := a + s;
				b := times!(b, a);
			}
			b;
		}
	}
}
