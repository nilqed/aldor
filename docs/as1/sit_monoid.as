------------------------------- sit_monoid.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"


define Monoid: Category == ExpressionType with {
        1: %;
	*: (%, %) -> %;
	^: (%, Integer) -> %;
	one?: % -> Boolean;
        times!: (%, %) -> %;
	default {
		macro copy?	== % has CopyableType;
		one?(a:%):Boolean	== a = 1;

		times!(a:%, b:%):% == {
			one? a => { copy?=>copy(b)$(% pretend CopyableType); b }
			a * b;
		}
	}
}
