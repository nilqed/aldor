------------------------------- sit_abmon.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"


define AbelianMonoid: Category == ExpressionType with {
	0: %;
        +: (%, %) -> %;
	*: (Integer, %) -> %;
	add!: (%, %) -> %;
	zero?: % -> Boolean;
	default {
		zero?(x:%):Boolean	== x = 0;

		add!(a:%, b:%):% == {
			zero? a => { % has CopyableType =>copy(b);b }
			a + b;
		}
	}
}
