------------------------------ sit_vector.as ------------------------------
-- Copyright (c) Marco Codutti 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995
-----------------------------------------------------------------------------

#include "algebra"

macro {
	ARR == Array;
	PA  == PrimitiveArray;
	I  == MachineInteger;
}


Vector(R:Join(AdditiveType, ExpressionType)):
	Join(AdditiveType, BoundedFiniteLinearStructureType R,
							ExpressionType) with {
		if R has ArithmeticType then {
			LinearCombinationType R;
			dot: (%, %) -> R;
		}
		if R has Ring then {
			random:        ()        -> %;
			random:        I        -> %;
		}
		if R has ArithmeticType then {
			tensor:	(%, %) -> %;
		}
		zero:		I	-> %;
		zero!:		%	-> ();
		zero?:		%	-> Boolean;
} == ARR R add {
	Rep == ARR R;

	0:%			== empty;
	zero(n:I):%		== { import from R; new(n, 0); }
	add!(u:%, v:%):%	== zip!(+$R, u, v);
	minus!(u:%, v:%):%	== zip!(-$R, u, v);
	(u:%) + (v:%):%		== zip(+$R, u, v);
	(u:%) - (v:%):%		== zip(-$R, u, v);
	minus!:% -> %		== map!(-$R);
	-:% -> %		== map(-$R);

	-- Vector's are 1-indexed while Array's are 0-indexed
	firstIndex:I		== 1;

	zero?(u:%):Boolean == {
		import from R;
		for x in u repeat { ~zero?(x) => return false; }
		true;
	}

	-- TEMPORARY: COMPILER BUG: firstIndex INLINED AS 0 FROM DEFAULT
	linearSearch(r:R, u:%):(Boolean, I, R) == linearSearch(r, u, 1);

	-- Vector's are 1-indexed while Array's are 0-indexed
	linearSearch(r:R, u:%, n:I):(Boolean, I, R) == {
		import from Rep;
		assert(n > 0); assert(n <= #u);
		(found?, index, value) := linearSearch(r, rep u, prev n);
		(found?, next index, value);
	}

	-- Vector's are 1-indexed while Array's are 0-indexed
	apply(u:%, n:I):R == {
		import from Rep, PA R;
		assert(n > 0); assert(n <= #u);
		data(rep u)(prev n);
	}

	-- Vector's are 1-indexed while Array's are 0-indexed
	set!(u:%, n:I, r:R):R == {
		import from Rep, PA R;
		assert(n > 0); assert(n <= #u);
		data(rep u)(prev n) := r;
	}

	-- Vector's are 1-indexed while Array's are 0-indexed
	zero!(u:%):() == {
		import from Rep, I, R, PA R;
		n := #u;
		assert(n >= 0);
		a := data rep u;
		for i in 0..prev n repeat a.i := 0;
	}

	zip(f:(R, R) -> R, u:%, v:%) : % == {
		import from I, Rep, PA R, R;
		assert(#u=#v);
		pu := data rep u; pv := data rep v;
		p:PA R := new(n := #v);
		for i in 0..prev n repeat p.i := f(pu.i, pv.i);
		per array(p, n);
	}

	zip!(f:(R, R) -> R, u:%, v:%) : % == {
		import from I, Rep, PA R, R;
		assert(#u=#v);
		pu := data rep u; pv := data rep v;
		for i in 0..prev(#v) repeat pu.i := f(pu.i, pv.i);
		u;
	}

	extree (v:%) : ExpressionTree == {
		import from List ExpressionTree, R;
		ExpressionTreeVector [extree x for x in v];
	}

	if R has ArithmeticType then {
		add!(v:%, r:R, w:%):% == zip!((x:R, y:R):R +-> x + r * y, v, w);

		(r:R) * (v:%):% == {
			zero? r => zero(#v);
			one? r => v;
			r = -1 => -v;
			map((x:R):R +-> r * x)(v);
		}

		dot(u:%, v:%):R == {
			import from I, R;
			assert(#u=#v);
			d:R := 0;
			for x in u for y in v repeat d := d + x * y;
			d;
		}

		tensor(u:%, v:%):% == {
			import from I, R, Rep;
			w := per new(#u * #v);
			k:I := 1;	-- Vector's are 1-indexed
			for x in u repeat for y in v repeat {
				w.k := x * y;
				k := next k;
			}
			w;
		}

		times! (r:R, v:%) : % == {
			zero? r => map!((x:R):R +-> 0)(v);
			one? r => v;
			r = -1 => minus! v;
			map!((x:R):R +-> r * x)(v);
		}
	}

	if R has Ring then {
		(n:Integer) * (p:%):% == { import from R; n::R * p; }

		random():% == { import from I; random(1+random()$I mod 100); }

		random (n:I) : % == {
			import from R;
			assert(n >= 0);
			u := zero n;
			for i in 1..n repeat u.i := random();
			u;
		}
	}
}

#if ALDORTEST
---------------------- test sit__vector.as --------------------------
#include "algebra"
#include "aldortest"

local inplace():Boolean == {
	macro R == Integer;
	macro V == Vector R;
	import from R,V,List R;

	u:V := [1,2,3,4,5,6];
	v:V := [6,5,4,3,2,1];
	w:V := [1,1,1,1,1,1];
	t := copy u;

	w := times!(7,w);
	u := add!(u,v);
	u ~= w => false;
	u := minus!(u,v);
	u ~= t => false;
	zero? add!( t, minus! u );
}

stdout << "Testing sit__vector..." << endnl;
aldorTest("in-place operations", inplace);
stdout << endnl;
#endif
