------------------------------- sit_char0.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1997
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"


define CharacteristicZero: Category == Ring with {
	default characteristic:Integer == 0;
}
