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
#include "sumit"

#if ASDOC
\thistype{QuotientCategory}
\History{Laurent Bernardin}{1/12/94}{created}
\History{Manuel Bronstein}{25/5/95}
{extracted the category from the type in order to create RationalCategory}
\History{Manuel Bronstein}{21/9/95}{added UnivariateGcdRing and gcd lifting}
\History{Manuel Bronstein}{21/3/96}{made it category of subrings}
\Usage{\this~R: Category}
\Params{ {\em R} & IntegralDomain & an integral domain\\ }
\Descr{\this~R is the category of subrings of the quotient fields of R.}
\begin{exports}
\category{IntegralDomain}\\
\category{DifferentialExtension R}\\
$*$: & (R,\%) $\to$ \% & multiplication by an integral element\\
coerce: & R $\to$ \% & coercion from R to \this\\
denominator: & \% $\to$ R & get the denominator of a quotient\\
normalize: & \% $\to$ \% & normalize a quotient\\
numerator: & \% $\to$ R & get the numerator of a quotient\\
\end{exports}
\begin{exports}[if R has CharacteristicZero then]
\category{CharacteristicZero}\\
\end{exports}
\begin{exports}[if R has FactorizationRing then]
\category{FactorizationRing}\\
\end{exports}
\begin{exports}[if R has FiniteCharacteristic then]
\category{FiniteCharacteristic}\\
\end{exports}
\begin{exports}[if R has LinearAlgebraRing then]
\category{LinearAlgebraRing}\\
\end{exports}
\begin{exports}[if R has OrderedRing then]
\category{OrderedRing}\\
\end{exports}
\begin{exports}[if R has RationalRootRing then]
\category{RationalRootRing}\\
\end{exports}
\begin{exports}[if R has Specializable then]
\category{Specializable}\\
\end{exports}
\begin{exports}[if R has UnivariateGcdRing then]
\category{UnivariateGcdRing}\\
\end{exports}
#endif

QuotientCategory(R: IntegralDomain): Category ==
	Join(IntegralDomain, DifferentialExtension R) with {
	if R has OrderedRing then OrderedRing;
	if R has CharacteristicZero then CharacteristicZero;
	if R has FiniteCharacteristic then FiniteCharacteristic;
	if R has Specializable then Specializable;
	if R has UnivariateGcdRing then UnivariateGcdRing;
	if R has RationalRootRing then RationalRootRing;
	if R has FactorizationRing then FactorizationRing;
	if R has LinearAlgebraRing then LinearAlgebraRing;
	*:		(R, %) -> %;
#if ASDOC
\aspage{$*$}
\Usage{r~\name~x}
\Signature{(R,\%)}{\%}
\Params{
{\em r} & R & An element of the ring.\\
{\em x} & \% & A quotient.\\
}
\Retval{Returns the product $r x$.}
#endif
	coerce:		R -> %;
#if ASDOC
\aspage{coerce}
\Usage{\name~x}
\Signature{R}{\%}
\Params{ {\em x} & R & An element of the ring\\ }
\Retval{Returns the quotient with numerator {\em x} and denominator 1.}
#endif
	denominator:	% -> R;
#if ASDOC
\aspage{denominator}
\Usage{\name~x}
\Signature{\%}{R}
\Params{ {\em x} & \% & A quotient\\ }
\Retval{Returns the denominator of a quotient.}
\seealso{numerator(\this)}
#endif
	normalize:	% -> %;
#if ASDOC
\aspage{normalize}
\Usage{\name~x}
\Signature{\%}{\%}
\Params{ {\em x} & \% & An quotient\\ }
\Descr{Normalize $x$ as much as possible given the category of $R$.}
#endif
	numerator:	% -> R;
#if ASDOC
\aspage{numerator}
\Usage{\name~x}
\Signature{\%}{R}
\Params{ {\em x} & \% & A quotient\\ }
\Retval{Returns the numerator of a quotient.}
\seealso{denominator(\this)}
#endif
	default {
		import from R;

		sample:%			== sample$R :: %;
		characteristic:Integer		== characteristic$R;
		coerce(a:Integer):%		== a::R::%;
		coerce(a:SingleInteger):%	== a::R::%;

		extree(a:%):ExpressionTree == {
			import from List ExpressionTree;
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
			specialization(F:Field):PartialFunction(%, F) == {
				import from PartialFunction(R, F), F, Partial F;
				f := partialMapping(specialization(F)$R);
				partialFunction((x:%):Partial(F) +-> {
					failed?(n := f numerator x) or
						failed?(d := f denominator x) or
							zero?(r := retract d) =>
								failed;
					[retract(n) / r];
				});
			}
		}
	}
}		
