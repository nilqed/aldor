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
------------------------------- sit_indvar.as ----------------------------------
--
-- Indexed variables, e.g. x_1, x_2, ...
--
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it ©INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{IndexedVariable}
\History{Manuel Bronstein}{10/3/2000}{created}
\Usage{import from \this~S\\ import from \this(S, x)}
\Params{
{\em S} & \astype{SumitType} & The type of the indices\\
        & \astype{TotallyOrderedType} & \\
{\em x} & \astype{Symbol} & The root variable (optional)\\
}
\Descr{\this~provides sorted symbols of the form $x_s$ where $s \in S$.}
\begin{exports}
\category{\astype{SumitType}}\\
\category{\astype{TotallyOrderedType}}\\
\asexp{index}: & \% $\to$ S & Index of a variable\\
\asexp{variable}: & S $\to$ \% & Create an indexed variable\\
\end{exports}
#endif

IndexedVariable(S:Join(SumitType, TotallyOrderedType), x:Symbol == new()):
	Join(SumitType, TotallyOrderedType) with {
		index: % -> S;
#if ALDOC
\aspage{index}
\Usage{\name~v}
\Signature{\%}{S}
\Params{{\em v} & \% & An indexed variable\\ }
\Retval{Returns the index of $v$.}
#endif
		variable: S -> %;
#if ALDOC
\aspage{variable}
\Usage{\name~s}
\Signature{S}{\%}
\Params{{\em s} & S & An index\\ }
\Retval{Returns the variable $x_s$.}
#endif
} == S add {
	Rep == S;

	index(v:%):S			== rep v;
	variable(s:S):%			== per s;
	local xtree:ExpressionTree	== extree x;

	extree(v:%):ExpressionTree == {
		import from S, List ExpressionTree;
		ExpressionTreeSubscript [xtree, extree index v];
	}

-- TEMPORARY: DEFAULT NOT FOUND OTHERWISE (1.1.12p4)
	(port:TextWriter) << (a:%):TextWriter == {
		import from ExpressionTree;
		tex(port, extree a);
	}
}
