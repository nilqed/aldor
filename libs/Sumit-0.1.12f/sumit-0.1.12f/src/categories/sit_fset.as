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
------------------------------ sit_fset.as ------------------------------
-- Copyright (c) Manuel Bronstein 1997
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1997
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{FiniteSet}
\History{Manuel Bronstein}{17/2/97}{created}
\Usage{\this: Category}
\Descr{\this~is the category of finite sets.}
\begin{exports}
\category{\astype{SumitType}}\\
\category{\astype{TotallyOrderedType}}\\
\asexp{\#}: & $\to$ \astype{Integer} & number of elements\\
\asexp{apply}: & (\%, \astype{ExpressionTree}) $\to$ \astype{ExpressionTree} &
Conversion to an expression tree\\
\asexp{index}: & \% $\to$ \astype{Integer} & Index of an element\\
\asexp{lookup}:
& \astype{Integer} $\to$ \% & Element with a given index\\
\asexp{random}: & () $\to$ \% & Get a random element\\
\end{exports}
#endif

macro {
	Z	== Integer;
	TREE	== ExpressionTree;
	anon	== (-"\Box");
}

define FiniteSet:Category == Join(SumitType, TotallyOrderedType) with {
	#: Z;
#if ALDOC
\aspage{\#}
\Usage{\name}
\Signature{}{\astype{Integer}}
\Retval{Returns the number of elements of the type.}
#endif
	apply: (%, TREE) -> TREE;
#if ALDOC
\aspage{apply}
\Usage{ \name(p, x)\\p~x }
\Signature{(\%, \astype{ExpressionTree})}{\astype{ExpressionTree}}
\Params{
{\em p} & \% & An element\\
{\em x} & \astype{ExpressionTree} & A name for the variables\\
}
\Retval{Returns p as an expression tree, using x as root variable name.}
#endif
	index: % -> Z;
#if ALDOC
\aspage{index}
\Usage{ \name~p }
\Signature{\%}{\astype{Integer}}
\Params{ {\em p} & \% & An element\\ }
\Retval{Returns the index of $p$.}
\seealso{lookup(\this)}
#endif
	lookup: Z -> %;
#if ALDOC
\aspage{lookup}
\Usage{ \name~j }
\Signature{\astype{Integer}}{\%}
\Params{ {\em j} & \astype{Integer} & An index \\ }
\Retval{Returns the element with index $j$.}
\seealso{index(\this)}
#endif
	random: () -> %;
#if ALDOC
\aspage{random}
\Usage{\name()}
\Signature{()}{\%}
\Retval{Returns a random element.}
#endif
	default {
		next(x:%):%	== { import from Z; lookup next index x; }
		prev(x:%):%	== { import from Z; lookup prev index x; }
		extree(x:%):TREE== { import from String,Symbol; x extree anon; }
		(x:%) < (y:%):Boolean	== { import from Z; index x < index y; }

		apply(x:%, t:TREE):TREE == {
			import from Z, List TREE;
			ExpressionTreeSubscript [t, extree index x];
		}

		random():% == {
			import from Z;
			lookup next(random()$Z mod #$%);
		}
	}
}
