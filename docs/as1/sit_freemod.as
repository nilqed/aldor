----------------------------- sit_freemod.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2001
-- Copyright (c) Marc Moreno Maza 2001
-- Copyright (c) INRIA 2001
-- Copyright (c) LIFL 2001
-----------------------------------------------------------------------------

#include "algebra"


define FreeModule(R:Join(ArithmeticType, ExpressionType)): Category ==
	FreeLinearCombinationType R with {
	if R has Ring then Module R;
        if R has GcdDomain then {
                content: % -> R;
                primitive: % -> (R, %);
                primitive!: % -> (R, %);
                primitivePart: % -> %;
                primitivePart!: % -> %;
	}
	term?: % -> Boolean;
	leadingCoefficient: % -> R;
	trailingCoefficient: % -> R;
	if R has Field then {
		monic: % -> %;
		monic!: % -> %;
	}
	nonZeroCoefficients: % -> Generator R;
	reductum: % -> %;
	reductum!: % -> %;
	support: % -> Generator Cross(R, %);
	default {
		term?(p:%):Boolean	== zero? reductum p;
		reductum!(p:%):%	== reductum p;

		nonZeroCoefficients(p:%):Generator R == generate {
			for term in support p repeat {
				(r, e) := term;
				yield r;
			}
		}

		map(f:R -> R)(p:%):% == {
			q:% := 0;
			for term in support p repeat {
				(c, n) := term;
				q := add!(q, f c, n);
			}
			q;
		}

		if R has Field then {
			-- TEMPORARY: WANT THOSE DEFS EVENTUALLY
			-- content(p:%):R		== 1;
			-- primitivePart(p:%):%	== p;
			-- primitive(p:%):(R, %)	== (1, p);

			monic(p:%):% == {
				import from R;
				zero? p or one?(a := leadingCoefficient p) => p;
				inv(a) * p;
			}

			monic!(p:%):% == {
				import from R;
				zero? p or one?(a := leadingCoefficient p) => p;
				times!(inv a, p);
			}
		}

		if R has GcdDomain then {
			local field?:Boolean	== R has Field;

			content(p:%):R == {
				field? => 1;
				gcd nonZeroCoefficients p;
			}

			primitivePart!(p:%):% == {
				field? => p;
				(c, q) := primitive! p;
				q;
			}

			primitivePart(p:%):% == {
				field? => p;
				(c, q) := primitive p;
				q;
			}

			primitive!(p:%):(R, %) == {
				import from R;
				field? => (1, p);
				one?(c := content p) => (c, p);
				(c, map!((r:R):R +-> quotient(r, c)) p);
			}

			primitive(p:%):(R, %) == {
				import from R;
				field? => (1, p);
				one?(c := content p) => (c, p);
				(c, map((r:R):R +-> quotient(r, c)) p);
			}
		}
	}
}

