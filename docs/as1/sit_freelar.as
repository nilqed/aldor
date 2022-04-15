----------------------------- sit_freelar.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2001
-- Copyright (c) INRIA 2001
-----------------------------------------------------------------------------

#include "algebra"


define FreeLinearArithmeticType(R:Join(ArithmeticType, ExpressionType)):
	Category == Join(FreeLinearCombinationType R, LinearArithmeticType R);

