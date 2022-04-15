-------------------------- sit_spfcat0.as ------------------------------
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"


macro {
	I == MachineInteger;
	A == PrimitiveArray;
}

define SmallPrimeFieldCategory0: Category == PrimeFieldCategory0 with {
	coerce: I -> %;
	machine: % -> I;
	discreteLogTable: Cross(A I, A I, Boolean);
	default {
		coerce(n:I):%	== { import from Integer; n::Integer::%; }
		machine(a:%):I	== { import from Integer; machine lift a; }

		(port:BinaryWriter) << (a:%):BinaryWriter == {
			import from I;
			port << machine a;
		}

		<< (port:BinaryReader):% == {
			import from I;
			(<< port)@I :: %;
		}

		discreteLogTable:Cross(A I, A I, Boolean) == {
			import from Boolean, I, A I;
			(new 0, new 0, false);
		}
	}
}
