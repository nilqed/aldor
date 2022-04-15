------------------------------- sit_ring.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "algebra"

macro Z == Integer;


define Ring: Category == Join(AbelianGroup, ArithmeticType, Monoid) with {
	characteristic: Z;
	coerce: Z -> %;
	factorial: (%, %, MachineInteger) -> %;
	random: () -> %;
	default {
		(x:%)^(n:MachineInteger):%	== x^(n::Z);
		(n:Z) * (x:%):%			== n::% * x;
		random():%			== random()$Z :: %;
		(x:%)^(n:Z):% == binaryExponentiation(x, n)$BinaryPowering(%,Z);

		factorial(a:%, s:%, n:MachineInteger):% == {
			assert(n >= 0);
			zero? n => 1;
			one? n => a;
			zero? a => 0;
			zero? s => a^n;
			b := a;
			for i in 2..n repeat {
				a := a + s;
				b := times!(b, a);
			}
			b;
		}
	}
}
