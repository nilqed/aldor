----------------------------- sit_automor.as ------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "algebra"


macro Z	== Integer;

Automorphism(R:Ring): Group with {
	apply: (%, R, n:Integer == 1) -> R;
	function: % -> (R -> R);
	morphism: (R -> R) -> %;
	morphism: (R -> R, R -> R) -> %;
	morphism: ((R, Z) -> R) -> %;
} == add {
	macro Rep == ((R, Z) -> R);

	1				== per((r:R, n:Z):R +-> r);
	inv(f:%):%			== per((r:R, n:Z):R +-> (rep f)(r, -n));
	(f:%)^(m:Z):%			== per((r:R, n:Z):R +-> (rep f)(r,n*m));
	morphism(f:(R, Z) -> R):%	== per f;
	morphism(f:R -> R, g:R -> R):%	== per((r:R,n:Z):R +-> iterat(f,g,n,r));
	morphism(f:R -> R):%		== morphism(f, noinverse);
	local iter(f:R->R, n:Z, r:R):R	== { for i in 1..n repeat r := f r; r }
	local ptr(f:%):Pointer		== f pretend Pointer;
	(u:%) = (v:%):Boolean		== { import from Pointer;ptr u = ptr v }
	apply(f:%, r:R, n:Z):R		== { zero? n => r; (rep f)(r, n) }
	function(f:%)(r:R):R		== { import from Z; f(r, 1) }

	extree(f:%):ExpressionTree == {
		import from Pointer, MachineInteger;
		extree(ptr(f)::MachineInteger);
	}

	local noinverse(r:R):R == {
		import from String;
		error "Morphism is not invertible";
	}

	local iterat(f:R->R, g:R->R, n:Z, r:R):R == {
		n < 0 => iter(g, -n, r);
		iter(f, n, r);
	}

	(f:%) * (g:%):% == {
		import from Z;
		f = g => f^2;
		per((s:R, n:Z):R +->
			iterat((r:R):R +-> f(g(r, 1), 1),
				(r:R):R +-> (inv g)((inv f)(r, 1), 1), n, s));
	}
}
