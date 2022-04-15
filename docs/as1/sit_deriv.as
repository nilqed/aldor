------------------------------ sit_deriv.as ----------------------------------
--
-- Derivations
--
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "algebra"


Derivation(R:Ring): Module R with {
	apply: (%, R, n:Integer == 1) -> R;
	derivation: (R -> R) -> %;
	function: % -> (R -> R);
} == add {
	macro Rep == R -> R;

	0			== per((r:R):R +-> 0);
	function(f:%):(R->R)	== rep f;
	-(f:%):%		== per((r:R):R +-> - (rep f) r);
	derivation(f:R -> R):%	== per f;
	(f:%) + (g:%):%		== per((r:R):R +-> (rep f)(r) + (rep g)(r));
	(u:%) = (v:%):Boolean	== { import from Pointer; address u = address v}
	(c:Integer) * (f:%):%	== { import from R; (c::R) * f }

	local address(u:%):Pointer == u pretend Pointer;

	(p:TextWriter) << (x:%):TextWriter == {
		import from Pointer;
		p << address x;
	}

	extree(u:%):ExpressionTree == {
		import from MachineInteger, Pointer;
		extree(address(u)::MachineInteger);
	}

	apply(f:%, r:R, n:Integer):R == {
		assert(n >= 0);
		g := function f;
		for i in 1..n repeat r := g r;
		r;
	}

	(c:R) * (f:%):% == {
		zero? c => 0;
		c = 1 => f;
		c = -1 => -f;
		per((r:R):R +-> c * (rep f) r);
	}
}
