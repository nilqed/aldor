----------------------------- sit_saexcpt.as --------------------------------
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"

ReducibleModulusException(R:CommutativeRing, m:R, a:R):
	ReducibleModulusExceptionType R == add {
		modulus:R == m;
		factor:R == a;
}

define ReducibleModulusExceptionType(R:CommutativeRing):Category == with {
	modulus: R;
	factor: R;
}

