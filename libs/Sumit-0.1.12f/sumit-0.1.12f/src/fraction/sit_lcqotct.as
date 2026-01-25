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
------------------------ sit_lcqotct.as ---------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I == MachineInteger;
	V == Vector;
}

#if ALDOC
\thistype{LinearCombinationFraction}
\History{Manuel Bronstein}{15/2/2000}{created}
\Usage{\this(R, LR, Q, LQ): Category}
\Params{
{\em R} & \astype{IntegralDomain} & an integral domain\\
{\em LR} & \astype{LinearCombinationType} R & a type over R\\
{\em Q} & \astype{FractionCategory} R & a fraction domain of R\\
{\em LQ} & \astype{LinearCombinationType} Q & a type over Q\\
}
\Descr{\this(R, LR, Q, LQ) is a category for domains providing conversions
between types integral and rational coefficients.}
\begin{exports}
\asexp{$*$}: & (Q, LR) $\to$ LQ & Product of a fraction by an integral element\\
\asexp{makeIntegral}: & LQ $\to$ (R, LR) & Conversion to an integral element\\
\asexp{makeRational}: & LR $\to$ LQ & Conversion to a rational element\\
\end{exports}
\begin{exports}[if Q has \astype{FractionByCategory0} R]
\asexp{makeIntegralBy}:
& LQ $\to$ (\astype{Integer}, LR) & Conversion to an integral element\\
\end{exports}
\begin{exports}[if Q has \astype{FractionFieldCategory0} R]
\asexp{normalize}: & LR $\to$ (R, LQ) & Conversion to a monic rational element\\
\end{exports}
#endif

define LinearCombinationFraction(R:IntegralDomain, LR:LinearCombinationType R,
	Q:FractionCategory R, LQ:LinearCombinationType Q): Category == with {
	*: (Q, LR) -> LQ;
#if ALDOC
\aspage{$\ast$}
\astarget{$*$}
\Usage{$c$ \name $A$}
\Signature{(Q, LR)}{LQ}
\Params{
{\em c} & Q & A fraction\\
{\em A} & LR & An integral element\\
}
\Retval{Returns $c A$ as a rational element.}
#endif
	makeIntegral: LQ -> (R, LR);
#if ALDOC
\aspage{makeIntegral}
\Usage{(a, A) := \name~B}
\Signature{LQ}{(R, LR)}
\Params{ {\em B} & LQ & A rational element\\ }
\Retval{Returns $(a, A)$ such that $A = a B$ is integral.
If R is a \astype{GcdDomain}, then $A$ is primitive.}
#endif
	if Q has FractionByCategory0 R then {
		makeIntegralBy: LQ -> (Integer, LR);
#if ALDOC
\aspage{makeIntegralBy}
\Usage{($\mu$, A) := \name~B}
\Signature{LQ}{(\astype{Integer}, LR)}
\Params{ {\em B} & LQ & A rational element\\ }
\Retval{Returns $(\mu, A)$ such that $A = \mbox{shift}(B, \mu)$ is integral.}
#endif
	}
	makeRational: LR -> LQ;
#if ALDOC
\aspage{makeRational}
\Usage{\name~A}
\Signature{LR}{LQ}
\Params{ {\em A} & LR & An integral element\\ }
\Retval{Returns $A$ as a rational element.}
#endif
	if Q has FractionFieldCategory0 R then {
		normalize: LR -> (R, LQ);
#if ALDOC
\aspage{normalize}
\Usage{(a, B) := \name~A}
\Signature{LR}{(R, LQ)}
\Params{ {\em A} & LR & An integral element\\ }
\Retval{Returns $(a, B)$ such that $A = a B$,
and $B$ is a normalized rational element.}
\Remarks{The normalization depends on the actual type LQ. For polynomial,
it means that the leading coefficient if $1$, for vectors that the first
coordinate is $1$, etc.}
#endif
	}
}
