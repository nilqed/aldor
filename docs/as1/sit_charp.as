------------------------------- sit_charp.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-------------------------------------------------------------------------------

#include "algebra"

macro {
	MZ == MachineInteger;
	Z  == Integer;
}

#include "sit_power"


define FiniteCharacteristic: Category == Ring with {
	pthPower: % -> %;
	pthPower!: % -> %;
	default {
		pthPower!(a:%):% == pthPower a;

		(a:%)^(n:Integer):% ==
			pExponentiation(a,
				n)$PthPowering(% pretend FiniteCharacteristic);
	}
}
