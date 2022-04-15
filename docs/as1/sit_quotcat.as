------------------------ quotcat.as ---------------------------
-- Copyright (c) Laurent Bernardin 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995
-----------------------------------------------------------------------------

#include "algebra"


define FractionCategory(R: IntegralDomain): Category ==
	Join(DifferentialExtension R, Algebra R, LinearAlgebraRing) with {
--	if R has OrderedRing then OrderedRing;
	if R has CharacteristicZero then CharacteristicZero;
	if R has FiniteCharacteristic then FiniteCharacteristic;
	if R has Specializable then Specializable;
	if R has UnivariateGcdRing then UnivariateGcdRing;
	if R has RationalRootRing then RationalRootRing;
	if R has FactorizationRing then FactorizationRing;
	denominator:	% -> R;
	numerator:	% -> R;
	normalize:	% -> %;
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
				Image has IntegralDomain =>
					partialFunction((x:%):Partial(Image)+->{
						failed?(n := f numerator x) or
						failed?(d := f denominator x) or
						zero?(r := retract d) => failed;
						exactQuotient(retract n, r);
					});
				partialFunction((x:%):Partial(Image)+->{
					failed?(n := f numerator x) or
					failed?(d := f denominator x) or
					failed?(r1 := reciprocal retract d) =>
									failed;
					[retract(n) * retract(r1)];
				});
			}
		}
	}
}		
