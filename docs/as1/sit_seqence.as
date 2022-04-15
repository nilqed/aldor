----------------------------- sit_seqence.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"

macro {
	I == MachineInteger;
	Z == Integer;
	S == Stream;
	V == Vector;
	TREE == ExpressionTree;
}


Sequence(R:Join(ArithmeticType, ExpressionType)):
	Join(LinearStructureType R, UnivariateFreeLinearArithmeticType R) with {
		#: % -> I;
		bound: % -> I;
		finite?: % -> Boolean;
		dot: V R -> V % -> %;
		interlacing: List % -> %;
		if R has Ring then {
			random: () -> %;
		}
		sequence: Stream R -> %;
} == S R add {
	Rep == S R;
	import from Rep;

	0:%				== sequence stream(0$R);
	1:%				== 1$R :: %;
	monom:%				== term(1$R, 1$Z);
	commutative?:Boolean		== commutative?$R;
	local dummy:Symbol		== { import from String; -"dummy" }
	coefficient(s:%, n:Z):R		== s(machine n);
	setCoefficient!(s:%,n:Z,c:R):%	== { s(machine n) := c; s }
	minus!(s:%):%			== { zero? s => 0; map!(-$R) s; }
	- (s:%):%			== { zero? s => 0; map(-$R) s; }
	map!(f:R -> R)(s:%):%		== sequence map!(f)(rep s);
	apply(s:%, x:TREE):TREE		== extree s;
	add!(s:%, c:R, n:Z, t:%):%	== add!(s, c * shift(t, n));
	coefficients(s:%):Generator R	== generator rep s;
	finite?(s:%):Boolean		== { import from I; 0 <= bound s }
	sequence(s:S R):%		== per s;
	bracket(g:Generator R):%	== { import from R;sequence stream(g,0)}
	(p:TextWriter) << (s:%):TextWriter	== p(s, dummy);

	if R has Ring then {
		random():% == { import from R; sequence stream(random$R) }
	}

	interlacing(l:List %):% == {
		import from List S R;
		assert(~empty? l);
		sequence interlacing [rep s for s in l];
	}

	bound(s:%):I == {
		import from Boolean, R, Partial R;
		(c, u) := constant rep s;
		c < 0 or ~zero?(retract u) => -1;
		c;
	}

	shift(s:%, n:Z):% == {
		import from I, Partial R;
		zero?(nn := machine n) or zero? s => s;
		(cs, u) := constant(rs := rep s);
		cs  < 0 => {
			nn < 0 => sequence stream(0, (m:I):R +-> rs(m-nn));
			sequence stream(0, (m:I):R +-> { m<nn => 0; rs(m-nn) });
		}
		c := retract u;
		nn < 0 => sequence stream(0, (m:I):R +-> rs(m-nn), cs+nn, c);
		sequence stream(0, (m:I):R +-> { m<nn=>0; rs(m-nn) }, cs+nn, c);
	}

	add!(s:%, c:R, n:Z):% == {
		assert(n >= 0);
		zero? s => term(c, n);
		nn := machine n;
		rs := rep s;
		rs.nn := rs.nn + c;
		s;
	}

	(s:%) = (t:%):Boolean == {
		import from Pointer, I, R, Partial R;
		(cs, us) := constant(rs := rep s);
		(ct, ut) := constant(rt := rep t);
		cs >= 0 => ct >= 0 and retract us = retract ut
						and equal?(rs, rt, max(cs, ct));
		ct < 0 and (s pretend Pointer) = (t pretend Pointer);
	}

	zero?(s:%):Boolean == {
		import from Z, R;
		zero? coefficient(s, 0) and constant? s;
	}

	one?(s:%):Boolean == {
		import from Z, R;
		one? coefficient(s, 0) and constant? s;
	}

	local constant?(s:%):Boolean == {
		import from I;
		(c, u) := constant rep s;
		zero? c;
	}

	term(c:R, n:Z):% == {
		import from I;
		zero? c => 0;
		nn := machine n;
		sequence stream(0, (m:I):R +-> { m = nn => c; 0 }, next nn, 0);
	}

	coerce(c:R):% == {
		import from I;
		zero? c => 0;
		sequence stream(0, (m:I):R +-> c, 1, 0);
	}

	map(f:R -> R)(s:%):% == {
		import from I, Partial R;
		(cs, us) := constant(rs := rep s);
		cs < 0 => sequence stream(0, (m:I):R +-> f(rs.m));
		sequence stream(0, (m:I):R +-> f(rs.m), cs, f(retract us));
	}

	dot(w:V R):V % -> % == {
		zero? w => { (v:V %):% +-> 0 }
		f := dotcoeff w;
		(v:V %):% +-> {
			import from I;
			assert(#v = #w);
			(c, vt) := constant v;
			c < 0 => sequence stream(0, (m:I):R +-> f(v, m));
			sequence stream(0, (m:I):R +-> f(v, m), c, dot(w, vt));
		}
	}

	local dotcoeff(w:V R):(V %, I) -> R == {
		import from I, R;
		assert(~zero? w);
		l:List Cross(R, I) := [(w.i, i) for i in 1..#w | ~zero?(w.i)];
		(v:V %, m:I):R +-> {
			s:R := 0;
			for pair in l repeat {
				(r, n) := pair;
				s := add!(s, r * (v.n)(m));
			}
			s;
		}
	}

	local constant(v:V %):(I, V R) == {
		import from Partial R, Stream R;
		m:I := -1;
		w:V R := zero(n := #v);
		for i in 1..n repeat {
			(c, u) := constant rep(v.i);
			failed? u => return(-1, w);
			if c > m then m := c;
		}
		(c, w);
	}

	local binary(s:%, t:%, f:(R, R) -> R):% == {
		import from I, Partial R;
		(cs, us) := constant(rs := rep s);
		(ct, ut) := constant(rt := rep t);
		cs < 0 or ct < 0 => sequence stream(0,(m:I):R +-> f(rs.m,rt.m));
		sequence stream(0, (m:I):R +-> f(rs.m, rt.m),
				max(cs, ct), f(retract us, retract ut));
	}

	(s:%) + (t:%):% == {
		zero? s => t;
		zero? t => s;
		binary(s, t, +$R);
	}

	(s:%) - (t:%):% == {
		zero? s => -t;
		zero? t => s;
		binary(s, t, -$R);
	}

	(s:%) * (t:%):% == {
		zero? s or zero? t => 0;
		binary(s, t, *$R);
	}

	(r:R) * (t:%):% == {
		zero? r => 0;
		one? r => t;
		map((x:R):R +-> r * x) t;
	}

	(s:%)^(n:I):% == {
		zero? s or one? n => s;
		zero? n => 1;
		map((x:R):R +-> x^n) s;
	}

	extree(s:%):TREE == {
		import from I, R, List TREE;
		ExpressionTreeList [extree(s.i) for i in 0..prev(#s)];
	}
}

