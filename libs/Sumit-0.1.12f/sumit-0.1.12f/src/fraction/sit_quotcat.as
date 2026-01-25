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
------------------------ quotcat.as ---------------------------
-- Copyright (c) Laurent Bernardin 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{FractionCategory}
\History{Laurent Bernardin}{1/12/94}{created}
\History{Manuel Bronstein}{25/5/95}
{extracted the category from the type in order to create RationalCategory}
\History{Manuel Bronstein}{21/9/95}{added UnivariateGcdRing and gcd lifting}
\History{Manuel Bronstein}{21/3/96}{made it category of subrings}
\Usage{\this~R: Category}
\Params{ {\em R} & \astype{IntegralDomain} & an integral domain\\ }
\Descr{\this~R is the category of subrings of the fraction field of R.}
\begin{exports}
\category{\astype{Algebra} R}\\
\category{\astype{DifferentialExtension} R}\\
\category{\astype{IntegralDomain}}\\
\category{\astype{LinearAlgebraRing}}\\
\asexp{denominator}: & \% $\to$ R & Denominator of a fraction\\
\asexp{normalize}: & \% $\to$ \% & Normalize a fraction\\
\asexp{numerator}: & \% $\to$ R & Numerator of a fraction\\
\end{exports}
\begin{exports}[if R has \astype{CharacteristicZero} then]
\category{\astype{CharacteristicZero}}\\
\end{exports}
\begin{exports}[if R has \astype{FactorizationRing} then]
\category{\astype{FactorizationRing}}\\
\end{exports}
\begin{exports}[if R has \astype{FiniteCharacteristic} then]
\category{\astype{FiniteCharacteristic}}\\
\end{exports}
% \begin{exports}[if R has \astype{OrderedRing} then]
% \category{\astype{OrderedRing}}\\
% \end{exports}
\begin{exports}[if R has \astype{RationalRootRing} then]
\category{\astype{RationalRootRing}}\\
\end{exports}
\begin{exports}[if R has \astype{Specializable} then]
\category{\astype{Specializable}}\\
\end{exports}
\begin{exports}[if R has \astype{UnivariateGcdRing} then]
\category{\astype{UnivariateGcdRing}}\\
\end{exports}
#endif

define FractionCategory(R: IntegralDomain): Category ==
	Join(IntegralDomain, DifferentialExtension R,
		Algebra R, LinearAlgebraRing) with {
--	if R has OrderedRing then OrderedRing;
	if R has CharacteristicZero then CharacteristicZero;
	if R has FiniteCharacteristic then FiniteCharacteristic;
	if R has Specializable then Specializable;
	if R has UnivariateGcdRing then UnivariateGcdRing;
	if R has RationalRootRing then RationalRootRing;
	if R has FactorizationRing then FactorizationRing;
	denominator:	% -> R;
	numerator:	% -> R;
#if ALDOC
\aspage{denominator,numerator}
\astarget{denominator}
\astarget{numerator}
\Usage{denominator~x\\ numerator~x}
\Signature{\%}{R}
\Params{ {\em x} & \% & A fraction\\ }
\Retval{Returns respectively the denominator and the numerator of a fraction.}
#endif
	normalize:	% -> %;
#if ALDOC
\aspage{normalize}
\Usage{\name~x}
\Signature{\%}{\%}
\Params{ {\em x} & \% & A fraction\\ }
\Descr{Normalize $x$ as much as possible given the category of $R$.}
#endif
	default {
		extree(a:%):ExpressionTree == {
			import from R, List ExpressionTree;
			zero? a => extree(0@R);
			tnum := extree numerator a;
			one? denominator a => tnum;
			tden := extree denominator a;
			-- move the minus sign out of the numerator to the front
			negative? tnum => {
				t := ExpressionTreeQuotient [negate tnum, tden];
				ExpressionTreeMinus [t];
			}
			ExpressionTreeQuotient [tnum, tden];
		}

		if R has Specializable then {
			specialization(Image:CommutativeRing):_
				PartialFunction(%,Image) == {
				import from PartialFunction(R, Image);
				import from Image, Partial Image;
				f := partialMapping(specialization(Image)$R);
				partialFunction((x:%):Partial(Image) +-> {
					failed?(n := f numerator x) or
					failed?(d := f denominator x) or
					zero?(r := retract d) => failed;
					exactQuotient(retract n, r);
				});
			}
		}
	}
}		
