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
----------------------------- sal_order.as ----------------------------------
--
-- This file defines ordered types
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro Z == MachineInteger;

#if ALDOC
\thistype{TotallyOrderedType}
\History{Manuel Bronstein}{28/9/98}{created}
\Usage{\this: Category}
\Descr{\this~is the category of totally ordered types.}
\begin{exports}
\category{\astype{PrimitiveType}}\\
\asexp{$<$}: & (\%, \%) $\to$ \astype{Boolean} & stricly less than\\
\asexp{$>$}: & (\%, \%) $\to$ \astype{Boolean} & stricly greater than\\
\asexp{$\le$}: & (\%, \%) $\to$ \astype{Boolean} & less than or equal to\\
\asexp{$\ge$}: & (\%, \%) $\to$ \astype{Boolean} & greater than or equal to\\
\asexp{max}: & (\%,\%) $\to$ \% & greater element\\
\asexp{min}: & (\%,\%) $\to$ \% & smaller element\\
\asexp{next}: & \% $\to$ \% & next greater element\\
\asexp{prev}: & \% $\to$ \% & next smaller element\\
\end{exports}
#endif

define TotallyOrderedType:Category == PrimitiveType with {
	<: (%, %) -> Boolean;
	>: (%, %) -> Boolean;
	<=: (%, %) -> Boolean;
	>=: (%, %) -> Boolean;
#if ALDOC
\aspage{$<,>,\le,\ge$}
\astarget{$<$}
\astarget{$>$}
\astarget{$\le$}
\astarget{$\ge$}
\Usage{$a < b$\\$a > b$\\$a \le b$\\$a \ge b$}
\Signature{(\%,\%)}{\astype{Boolean}}
\Params{ {\em a, b} & \% & elements of the type\\}
\Retval{$a < b$, $a > b$, $a \le b$, $a \ge b$ return \true~when
$a$ is respectively stricly smaller than, stricly greater than,
less than or equal to, greater than or equal to $b$.}
#endif
	max: (%, %) -> %;
	min: (%, %) -> %;
#if ALDOC
\aspage{max,min}
\astarget{max}
\astarget{min}
\Usage{max(x,y)\\min(x,y)}
\Signature{(\%,\%)}{\%}
\Params{ {\em a, b} & \% & elements of the type\\}
\Retval{max(a,b) and min(a,b) respectively the largest and the smallest
among a and b.}
#endif
	next: % -> %;
	prev: % -> %;
#if ALDOC
\aspage{next,prev}
\astarget{next}
\astarget{prev}
\Usage{next~a\\prev~a}
\Signature{\%}{\%}
\Params{ {\em a} & \% & element of the type\\}
\Retval{next(a) and prev(a) return the first element
strictly greater, respectively smaller, than $a$.}
#endif
	default {
		(a:%) > (b:%):Boolean	== ~(a <= b);
		(a:%) >= (b:%):Boolean	== ~(a < b);
		(a:%) <= (b:%):Boolean	== (a < b) or (a = b);
		max(a:%, b:%):%		== { a < b => b; a };
		min(a:%, b:%):%		== { a < b => a; b };
	}
};

