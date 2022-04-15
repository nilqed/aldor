----------------------------- sit_ufalg.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "algebra"

macro Z == Integer;


define UnivariateFreeLinearArithmeticType(R:Join(ArithmeticType, ExpressionType)):
	Category == IndexedFreeLinearArithmeticType(R, Z) with {
	apply: (%, ExpressionTree) -> ExpressionTree;
	apply: (TextWriter, %, Symbol) -> TextWriter;
	coefficients: % -> Generator R;
	monom: %;
	shift: (%, Z) -> %;
	shift!: (%, Z) -> %;
	truncate: (%, Z) -> %;
	truncate!: (%, Z) -> %;
	default {
		coerce(c:R):%		== { import from Z; term(c, 0); }
		monom:%			== { import from Z; monomial 1; }
		shift!(p:%, n:Z):%	== shift(p, n);
		truncate!(p:%, n:Z):%	== truncate(p, n);

		truncate(p:%, n:Z):% == {
			assert(n >= 0);
			q:% := 0;
			for i in prev(n)..0 by -1 repeat
				q := add!(q, coefficient(p, i), i);
			q;
		}

		apply(port:TextWriter, p:%, v:Symbol):TextWriter == {
			import from ExpressionTree;
			-- tex(port, p extree v);
			infix(port, p extree v);
		}
	}
}
