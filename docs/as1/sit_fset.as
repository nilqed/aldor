------------------------------ sit_fset.as ------------------------------
-- Copyright (c) Manuel Bronstein 1997
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1997
-----------------------------------------------------------------------------

#include "algebra"


macro {
	Z	== Integer;
	TREE	== ExpressionTree;
	anon	== (-"\Box");
}

define FiniteSet:Category == Join(ExpressionType, TotallyOrderedType) with {
	#: Z;
	apply: (%, TREE) -> TREE;
	index: % -> Z;
	lookup: Z -> %;
	random: () -> %;
	default {
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
