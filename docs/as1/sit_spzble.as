------------------------------- sit_spzble.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "algebra"


define Specializable: Category == with {
	specialization: (Image:CommutativeRing) -> PartialFunction(%, Image);
}
