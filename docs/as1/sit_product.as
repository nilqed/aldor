------------------------------- sit_product.as -------------------------------
--
-- Formal products, used for example for factorisation results
--
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "algebra"


macro {
	A	== PrimitiveArray;
	Z	== Integer;
}

Product(R:CommutativeRing): Join(CopyableType, Monoid) with {
	#: % -> MachineInteger;
	divisors: % -> Generator %;
	expand: % -> R;
	expandFraction: % -> (R, R);
	generator: % -> Generator Cross(R, Z);
	log: (M:AbelianMonoid, R -> M) -> % -> M;
	term: (R, Z) -> %;
	times!: (%, R, Z) -> %;
} == add {
	-- TEMPORARY: workaround to bug 1187
	local TERM: PrimitiveType with {
		maketerm: (R, Z) -> %;
		exponent: % -> Z;
		coefficient: % -> R;
	} == add {
		macro Rep == Record(trm:R, exp:Z);

		maketerm(x:R, n:Z):%	== { import from Rep; per [x, n] }
		exponent(t:%):Z		== { import from Rep; rep(t).exp }
		coefficient(t:%):R	== { import from Rep; rep(t).trm }

		(a:%) = (b:%):Boolean == {
			import from R, Z;
			exponent a = exponent b
				and coefficient a = coefficient b;
		}
	}

	macro {
		-- TEMPORARY: workaround to bug 1187
		-- TERM	== Record(trm:R, exp:Z);
		Rep	== List TERM;
	}

	import from TERM, Rep;

	1:%				== per empty;
	-- TEMPORARY: workaround to bug 1187
	-- local exponent(term:TERM):Z	== term.exp;
	-- local coefficient(term:TERM):R	== term.trm;
	#(p:%):MachineInteger		== # rep p;
	copy(p:%):%			== per copy rep p;
	divisors(x:%):Generator %	== div rep x;

	term(x:R, n:Z):% == {
		zero? n or one? x => 1;
		-- TEMPORARY: workaround to bug 1187
		-- per [[x, n]];
		per [maketerm(x, n)];
	}

	log(M:AbelianMonoid, rlog:R -> M)(x:%):M == {
		import from Z;
		m:M := 0;
		for t in x repeat {
			(c, n) := t;
			m := add!(m, n * rlog c);
		}
		m;
	}

	generator(x:%):Generator Cross(R, Z) == generate {
		for t in rep x repeat yield(coefficient t, exponent t);
	}

	local div(l:Rep):Generator % == generate {
		import from Z;
		if empty? l then yield 1;
		else {
			t := first l;
			c := coefficient t;
			n := exponent t;
			for d in div rest l repeat
				for i in 0..n repeat yield(term(c, i) * d);
		}
	}

	(x:%) ^ (m:Z):% == {
		import from R;
		y:% := 1;
		zero? m => y;
		for t in x repeat {
			(c, n) := t;
			if one? c then y := times!(y, c, n);
				else y := times!(y, c, m * n);
		}
		y;
	}

	-- very naive for now, no simplification whatsoever
	(a:%) * (b:%):% == {
		one? a => b; one? b => a;
		p := copy b;
		for t in a repeat {
			(c, n) := t;
			p := times!(p, c, n);
		}
		p;
	}

	times!(p:%, x:R, n:Z):% == {
		zero? n or one? x => p;
		per cons(first rep term(x, n), rep p);
	}

	-- very ineficient for now!
	(a:%) = (b:%):Boolean == {
		import from R;
		(na, da) := expandFraction a;
		(nb, db) := expandFraction b;
		na * db = nb * da;
	}

	expand(x:%):R == {
		a:R := 1;
		for t in x repeat {
			(c, n) := t;
			a := times!(a, c^n);
		}
		a;
	}

	expandFraction(x:%):(R, R) == {
		import from Z;
		n:R := 1;
		d:R := 1;
		for t in x repeat {
			(c, e) := t;
			if e > 0 then n := times!(n, c^e);
				else d := times!(d, c^(-e));
		}
		(n, d);
	}

	extree(x:%):ExpressionTree == {
		import from R, List ExpressionTree;
		l := [term2tree(coefficient t, exponent t) for t in rep x];
		empty? l => extree(1$R);
		empty? rest l => first l;
		ExpressionTreeTimes l;
	}

	local term2tree(g:R, c:Z):ExpressionTree == {
		import from List ExpressionTree;
		assert(c ~= 0);
		tg := extree g;
		one? c => tg;
		tc := extree c;
		ExpressionTreeExpt [tg, tc];
	}
}
