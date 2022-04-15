------------------------   sit_matcat.as   -----------------------
-- Copyright (c) Marco Codutti 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995
-----------------------------------------------------------------------------

#include "algebra"

macro {
	I == MachineInteger;
	V == Vector;
}


define MatrixCategory(R: Join(ArithmeticType, ExpressionType)): Category ==
	Join(CopyableType, LinearArithmeticType R) with {
	if R has SerializableType then SerializableType;
	*:              (%,V R) -> V R;
	bracket: Tuple V R -> %;
	bracket: Generator V R -> %;
	apply:          (%,I,I) -> R;
	apply:          (%,I,I,I,I) -> %;
	apply:		(%, Array I, Array I) -> %;
	colCombine!:	 (%,R,I,R,I) -> %;
	colCombine!:	 (%,R,I,R,I,I,I) -> %;
	colCombine!:    (%,(R,R)->R,I,I) -> %;
	colCombine!:    (%,(R,R)->R,I,I,I,I) -> %;
	rowCombine!:	 (%,R,I,R,I) -> %;
	rowCombine!:	 (%,R,I,R,I,I,I) -> %;
	rowCombine!:    (%,(R,R)->R,I,I) -> %;
	rowCombine!:    (%,(R,R)->R,I,I,I,I) -> %;
	colSwap!:	(%,I,I) -> %;
	colSwap!:	(%,I,I,I,I) -> %;
	rowSwap!:	(%,I,I) -> %;
	rowSwap!:	(%,I,I,I,I) -> %;
	column: (%, I) -> V R;
	row: (%, I) -> V R;
	columns: % -> Generator V R;
	rows: % -> Generator V R;
	companion:	(V R, a:R == 1) -> %;
	diagonal:	V R -> %;
	diagonal:	(R, I) -> %;
	diagonal?:	% -> Boolean;
	scalar?:	% -> Boolean;
	square?:	% -> Boolean;
	dimensions:     % -> (I,I);
	map:		(R -> R) -> V R -> %;
	map:		(R -> R) -> % -> %;
	map!:		(R -> R) -> % -> %;
	numberOfColumns:	% -> I;
	numberOfRows:		% -> I;
	one:           I -> %;
	one?:		% -> Boolean;
	if R has Ring then {
		random: () -> %;
		random: (I,I) -> %;
	}
	set!:          (%,I,I,R) -> R;
	setMatrix!:	(%,I,I,%) -> %;
	tensor: (%, %) -> %;
	transpose:	V R -> %;
	transpose:	% -> %;
	transpose!:	% -> %;
	if R has DifferentialRing then {
		wronskian: V R -> %;
}
	zero:           (I, I) -> %;
	zero!:		% -> ();
	zero?:		% -> Boolean;

#if NOMOREBLOODYCOMPILERBUGS
	default {
	commutative?:Boolean	== false;
	copy:% -> %		== map((r:R):R +-> r);
	-: % -> %		== map((r:R):R +-> -r);
	minus!: % -> %		== map!((r:R):R +-> -r);
	map(f:R -> R):% -> %	== (a:%):% +-> map!(f)(copy a);
	colSwap!(a:%,i:I,j:I):%	== colSwap!(a,i,j,1,numberOfRows a);
	rowSwap!(a:%,i:I,j:I):%	== rowSwap!(a,i,j,1,numberOfColumns a);
	numberOfRows(a:%):I	== { (r,c) := dimensions a; r; }
	numberOfColumns(a:%):I	== { (r,c) := dimensions a; c; }
	tensor(a:%, b:%):%	== transpose [tensorGen(a, b)];
	(a:%)^(n:I):%		== { import from Integer; a^(n::Integer); }
	one(n:I):%		== { import from R; diagonal(1, n); }
	coerce(r:R):%		== { import from I; diagonal(r, 1); }

	colCombine! (a:%,c1:R,i1:I,c2:R,i2:I) : % ==
		colCombine! (a,c1,i1,c2,i2,1,numberOfRows a);

	colCombine! (a:%,c1:R,i1:I,c2:R,i2:I,j1:I,j2:I) : % ==
		colCombine! (a,(x:R,y:R):R +-> c1*x+c2*y, i1,i2,j1,j2);

	colCombine! (a:%,f:(R,R)->R,i1:I,i2:I) : % ==
		colCombine! (a,f,i1,i2,1,numberOfRows a);

	rowCombine! (a:%,c1:R,i1:I,c2:R,i2:I) : % ==
		rowCombine! (a,c1,i1,c2,i2,1,numberOfColumns a);

	rowCombine! (a:%,c1:R,i1:I,c2:R,i2:I,j1:I,j2:I) : % ==
		rowCombine! (a,(x:R,y:R):R +-> c1*x+c2*y, i1,i2,j1,j2);

	rowCombine! (a:%,f:(R,R)->R,i1:I,i2:I) : % ==
		rowCombine! (a,f,i1,i2,1,numberOfColumns a);

	map(f:R -> R)(v:V R):% == {
		n := #v;
		a := zero(n, n);
		for j in 1..n repeat a(1,j) := v.j;
		for i in 2..n repeat for j in 1..n repeat
			a(i, j) := f a(prev i, j);
		a;
	}

	square?(a:%):Boolean == {
		import from I;
		(n, m) := dimensions a;
		n = m;
	}

	column(a:%, j:I):V R == {
		(n, m) := dimensions a;
		assert(j > 0); assert(j <= m);
		[a(i, j) for i in 1..n];
	}

	row(a:%, i:I):V R == {
		(n, m) := dimensions a;
		assert(i > 0); assert(i <= n);
		[a(i, j) for j in 1..m];
	}

	columns(a:%):Generator V R == generate {
		import from I;
		n := numberOfColumns a;
		for i in 1..n repeat yield column(a, i);
	}

	rows(a:%):Generator V R == generate {
		import from I;
		n := numberOfRows a;
		for i in 1..n repeat yield row(a, i);
	}

	(a:%) ^ (n:Integer):% == {
		assert(n >= 0);
		assert(square? a);
		zero? n => one numberOfRows a;
		one? n => a;
		b := copy a;
		for i in 2..n repeat b := times!(b, a);
		b;
	}

	(c:R) * (a:%):% == {
		zero? c => zero dimensions a;
		one? c => a;
		c = -1 => -a;
		map((r:R):R +-> c * r)(a);
	}

	times!(c:R, a:%):% == {
		zero? c => map!((r:R):R +-> 0)(a);
		one? c => a;
		c = -1 => minus! a;
		map((r:R):R +-> c * r)(a);
	}

	companion (l:V R, a:R == 1):% == {
		import from I, R;
		n := #l;
		assert(n>0);
		o := zero(n,n);
		for i in 1..prev n repeat {
			o(i,n) := l.i;
			o(next i, i) := a;
		}
		o(n, n) := l.n;
		o;
	}

	diagonal (a:R, n:I): % == {
		assert(n>0);
		o := zero(n,n);
		for i in 1..n repeat o(i,i) := a;
		o;
	}

	diagonal (l:V R): % == {
		import from I;
		n := #l;
		assert(n>0);
		o := zero(n,n);
		for i in 1..n repeat o(i,i) := l.i;
		o;
	}

	diagonal?(a:%) : Boolean == {
		import from I, R;
		(n,m) := dimensions a;
		n ~= m => false;
		for i in 1..n repeat {
			for j in 1..m | i ~= j repeat
				~zero?(a(i,j)) => return false;
		}
		true;
	}

	scalar?(a:%):Boolean == {
		import from I, R;
		(n,m) := dimensions a;
		n ~= m => false;
		zero? n => true;
		p := a(1,1);
		for i in 1..n repeat {
			i > 1 and a(i,i) ~= p => return false;
			for j in 1..m | i ~= j repeat
				~zero?(a(i,j)) => return false;
		}
		true;
	}

	one?(a:%):Boolean == {
		import from I, R;
		(r, c) := dimensions a;
		r > 0 and c > 0 and one?(a(1, 1)) and scalar? a;
	}

	extree (a:%) : ExpressionTree == {
		import from I, R, V R, List ExpressionTree;
		(r, c) := dimensions a;
		l := [extree r, extree c];
		for v in rows a repeat l := append!(l, [extree x for x in v]);
		ExpressionTreeMatrix l;	
	}

	local tensorGen(a:%, b:%):Generator V R == generate {
		import from V R;
		for u in rows a repeat for v in rows b repeat yield tensor(u,v);
	}

	if R has DifferentialRing then {
		wronskian(v:V R):% == {
			import from R;
			map(differentiate) v;
		}
	}

	if R has Ring then {
		random():% == {
			import from I;
			random(1+random()$I mod 100, 1+random()$I mod 100);
		}
	}
	}
#endif
}


MatrixCategory2(R:Join(ExpressionType, ArithmeticType), MR:MatrixCategory R,
	S:Join(ExpressionType, ArithmeticType), MS:MatrixCategory S): with {
		map: (R -> S) -> MR -> MS;
} == add {
	map(f:R -> S)(m:MR):MS == {
		import from MachineInteger;
		(r, c) := dimensions m;
		mm:MS := zero(r, c);
		for i in 1..r repeat for j in 1..r repeat mm(i,j) := f m(i, j);
		mm;
	}
}
