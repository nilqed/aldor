------------------------------ sit_group.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"


define Group: Category == Monoid with {
	/: (%, %) -> %;
	inv: % -> %;
	default (x:%) / (y:%):% == x * inv y;
}
