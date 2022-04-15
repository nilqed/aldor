------------------------------- sit_indvar.as ----------------------------------
--
-- Indexed variables, e.g. x_1, x_2, ...
--
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it ©INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"


IndexedVariable(S:Join(ExpressionType, TotallyOrderedType), x:Symbol == new()):
	Join(ExpressionType, TotallyOrderedType) with {
		index: % -> S;
		variable: S -> %;
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
