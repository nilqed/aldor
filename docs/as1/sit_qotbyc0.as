------------------------ sit_qotbyc0.as ---------------------------
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"

macro Z == Integer;


define FractionByCategory0(R:IntegralDomain):Category==FractionCategory R with {
	order: % -> Z;
	shift: (%, Z) -> %;
}
