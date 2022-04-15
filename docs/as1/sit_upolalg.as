----------------------------- sit_upolalg.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"

macro {
	I	== MachineInteger;
	Z	== Integer;
}


define UnivariatePolynomialRing(R:Join(ArithmeticType, ExpressionType)):
	Category == UnivariateFreeRing R with {
	if R has Parsable then Parsable;
	add!: (%, R, Z, %, Z, Z) -> %;
	compose: (%, %) -> %;
	translate: (%, R) -> %;
	default {
		local dummy:Symbol == { import from String; -"dummy"; }

		translate(p:%, r:R):% == {
			zero? r => p;
			compose(p, monom - r::%);
		}

		add!(p:%, c:R, n:Z, q:%):% ==
			add!(p, c, n, q, 0, max(degree p, degree q + n));

		apply(p:%, x:ExpressionTree):ExpressionTree == {
			import from Boolean, R, List ExpressionTree;
			import from UnivariateMonomial(R, dummy);
			zero? p => extree(0@R);
			l:List(ExpressionTree) := empty;
			for term in p repeat {
				m := monomial(term)@UnivariateMonomial(R,dummy);
				l := cons(m x, l);
			}
			assert(~empty? l);
			empty? rest l => first l;
			ExpressionTreePlus reverse! l;
		}

		compose(p:%, q:%):% == {
			import from Z;
			q = monom => p;
			pq:% := 0;
			zero? q => pq;
			qn:% := 1;
			d:Z := 0;
			for term in terms p repeat {	-- low to high
				(c, n) := term;
				for i in 1..n - d repeat
					zero?(qn := q * qn) => return pq;
				pq := add!(pq, c * qn);
				d := n;
			}
			pq;
		}

		if R has Parsable then {
			import from ExpressionTree;
			-- TEMPORARY: CONSTANT CAUSE RUNTIME BOMB (1173)
			-- local xtree:ExpressionTree	== extree monom;
			-- local xtree?:Boolean		== leaf? xtree;
			local xtree():ExpressionTree	== extree monom;
			local xtree?():Boolean		== leaf? xtree();

			eval(l:ExpressionTreeLeaf):Partial % == {
				import from R, Partial R;
				-- xtree? and l = leaf xtree => [monom];
				xtree?() and l = leaf xtree() => [monom];
				failed?(u := eval(l)$R) => failed;
				[retract(u)::%];
			}

			eval(p:MachineInteger,l:List ExpressionTree):Partial %==
			{
				import from R, Partial R, ParsingTools %;
				failed?(u := evalArith(p, l)) => {
					failed?(v := eval(p, l)$R) => failed;
					[retract(v)::%];
				}
				u;
			}
		}
	}
}
