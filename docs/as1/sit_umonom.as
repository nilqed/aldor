----------------------------- sit_umonom.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "algebra"


macro {
	Z == Integer;
	TREE == ExpressionTree;
}

UnivariateMonomial(R:Join(ArithmeticType, ExpressionType), var:Symbol == new()):
	ExpressionType with {
	apply: (%, TREE) -> TREE;
	coefficient: % -> R;
	degree: % -> Z;
	map: (R -> R) -> % -> %;
	map!: (R -> R) -> % -> %;
	monomial: (R, Z) -> %;
	if R has FiniteCharacteristic then {
        	pthPower: % -> %;
        	pthPower!: % -> %;
	}
	setCoefficient!: (%, R) -> R;
	setDegree!: (%, Z) -> Z;
} == add {
	Rep == Record(coef:R, expt:Z);
	import from Rep;

	local evar:TREE				== extree var;
	monomial(c:R, n:Z):%			== { assert(n>=0); per [c, n]; }
	coefficient(t:%):R     			== rep(t).coef;
	degree(t:%):Z    	  		== rep(t).expt;
	setDegree!(t:%, n:Z):Z			== rep(t).expt := n;
	setCoefficient!(t:%, c:R):R		== rep(t).coef := c;
	extree(p:%):TREE			== p evar;
	map(f:R -> R)(p:%):%	== monomial(f coefficient p, degree p);
	map!(f:R -> R)(p:%):%	== { setCoefficient!(p, f coefficient p); p }

	apply(p:%, t:TREE):TREE == {
		import from R, List TREE;
		zero?(c := coefficient p) => extree c;
		d := degree p;
		negative?(tc := extree c) =>
			ExpressionTreeMinus [tree(c ~= -1, negate tc, d, t)];
		tree(c ~= 1, tc, d, t);
	}

	local tree(tims?:Boolean, c:TREE, n:Z, t:TREE):TREE == {
		import from R, List TREE;
		zero? n => c;
		if n > 1 then t := ExpressionTreeExpt [t, extree n];
		tims? => ExpressionTreeTimes [c, t];
		t;
	}

	(u:%) = (v:%):Boolean == {
		degree u = degree v and coefficient u = coefficient v;
	}

	if R has FiniteCharacteristic then {
		pthPower(p:%):% ==
			monomial(pthPower(coefficient p)$R,
					characteristic$R * degree p);

		pthPower!(p:%):% == {
			rec := rep p;
			rec.coef := pthPower(rec.coef)$R;
			rec.expt := characteristic$R * rec.expt;
			p;
		}
	}
}

#if ALDORTEST
---------------------- test umonom.as --------------------------
#include "algebra"
#include "aldortest"

macro {
        Z == Integer;
	F == SmallPrimeField 11;
        M == UnivariateMonomial;
}

local double(a:Z):Z == a + a;

local degree():Boolean == {
        import from Z, M Z;
        p := monomial(2, 3);
	q := map(double)(p);
        degree p = 3 and coefficient p = 2 and
		degree q = degree p and coefficient q = 4;
}

local pthpower():Boolean == {
        import from MachineInteger, Z, F, M F;

        p := monomial(2*1, 3);
	q := pthPower p;
	degree p = 3 and coefficient p = 2*1 and
		degree q = characteristic$F * degree p
			and coefficient q = coefficient p;
}

stdout << "Testing umonom..." << endnl;
aldorTest("degree", degree);
aldorTest("pthpower", pthpower);
stdout << endnl;
#endif

