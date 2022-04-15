------------------------ sit_lcqotct.as ---------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"

macro {
	I == MachineInteger;
	V == Vector;
}


define LinearCombinationFraction(R:IntegralDomain, LR:LinearCombinationType R,
	Q:FractionCategory R, LQ:LinearCombinationType Q): Category == with {
	*: (Q, LR) -> LQ;
	makeIntegral: LQ -> (R, LR);
	if Q has FractionByCategory0 R then {
		makeIntegralBy: LQ -> (Integer, LR);
	}
	makeRational: LR -> LQ;
	if Q has FractionFieldCategory0 R then {
		normalize: LR -> (R, LQ);
	}
}
