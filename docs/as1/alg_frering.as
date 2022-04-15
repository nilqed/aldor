----------------------------- alg_frering.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2004
-- Copyright (c) Marc Moreno Maza 2004
-- Copyright (c) INRIA 2004
-- Copyright (c) LIFL 2004
-----------------------------------------------------------------------------

#include "algebra"


define FreeRRing(R:Join(ArithmeticType, ExpressionType)):
	Category == Join(FreeModule R, FreeLinearArithmeticType R) with {
	if R has Ring then RRing R;
	if R has CharacteristicZero then CharacteristicZero;
	if R has FiniteCharacteristic then FiniteCharacteristic;
	if R has RittRing then RittRing;
	ground?: % -> Boolean;
	default {
		ground?(x:%):Boolean == leadingCoefficient(x)::% = x;
		if R has RittRing then
			inv(n:Integer):% == { import from R; inv(n)$R :: % };
	}
}

