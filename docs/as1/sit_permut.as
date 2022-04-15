----------------------- sit_permut.as -----------------------------
--
-- Permutations of a finite numbe of elements
--
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"

macro {
	Z == MachineInteger;
	A == PrimitiveArray;
}


Permutation(n:Z):Join(CopyableType, Group) with {
	apply: (%, Z) -> Z;
	mapping: % -> (Z -> Z);
	sign: % -> Z;
	transpose: (Z, Z) -> %;
	transpose!: (%, Z, Z) -> %;
} == {
	assert(n >= 0);
	add {
	Rep == A Z;	-- rep(s).i == s.i for 0 < i <= n
			-- rep(s).0 = sign(s)
			-- rep(s)(n+1) = 1 if s is the constant 1, 0 otherwise

	
	local nplus1:Z			== next n;
	local nplus2:Z			== next nplus1;
	local setsign!(s:%, e:Z):Z	== { import from Rep; rep(s).0 := e; }
	sign(s:%):Z			== { import from Rep; rep(s).0 }
	mapping(s:%):Z -> Z		== { (i:Z):Z +-> s i }
	one?(s:%):Boolean		== constant1?(s) or s = 1;

	local setConst1!(s:%):%	== {
		import from Rep;
		rep(s).nplus1 := 1;
		s;
	}

	local newperm():% == {
		import from Rep;
		a := new nplus2;
		a(nplus1) := 0;		-- force non-constant 1
		per a;
	}

	local constant1?(s:%):Boolean == {
		import from Rep;
		one?(rep(s)(nplus1));
	}

	(s:%) = (t:%):Boolean == {
		import from Z;
		constant1? s and constant1? t => true;
		for i in 1..n repeat {
			s.i ~= t.i => return false;
		}
		true;
	}

	extree(s:%):ExpressionTree == {
		import from Z, List ExpressionTree;
		ExpressionTreeList [extree(s i) for i in 1..n];
	}

	apply(s:%, i:Z):Z == {
		import from Rep;
		assert(i > 0); assert(i <= n);
		rep(s).i;
	}

	local set!(s:%, i:Z, j:Z):Z == {
		import from Rep;
		assert(i > 0); assert(i <= n);
		assert(j > 0); assert(j <= n);
		rep(s).i := j;
	}

	copy(s:%):% == {
		import from Z;
		constant1? s => s;
		s0 := newperm();
		setsign!(s0, sign s);
		for i in 1..n repeat s0.i := s i;
		s0;
	}

	local ident():% == {
		import from Z;
		s := newperm();
		setsign!(s, 1);
		for i in 1..n repeat s.i := i;
		s;
	}
	1:% == setConst1! ident();

	transpose(i:Z, j:Z):% == {
		assert(i > 0); assert(i <= n);
		assert(j > 0); assert(j <= n);
		i = j => 1;
		s := ident();
		setsign!(s, -1);
		s.i := j;
		s.j := i;
		s;
	}

	-- replaces s by (i j) s
	transpose!(s:%, i:Z, j:Z):% == {
		assert(i > 0); assert(i <= n);
		assert(j > 0); assert(j <= n);
		i = j => s;
		constant1? s => transpose(i, j);
		setsign!(s, -sign s);
		t := s.i;
		s.i := s.j;
		s.j := t;
		s;
	}

	inv(s:%):% == {
		import from Z;
		one? s => s;
		s1 := newperm();
		setsign!(s1, sign s);
		for i in 1..n repeat s1(s i) := i;
		s1;
	}

	(s:%) / (t:%):% == {
		import from Z;
		one? t => s;
		st := newperm();
		setsign!(st, sign(s) * sign(t));
		for i in 1..n repeat st(t i) := s i;
		st;
	}

	(s:%) * (t:%):% == {
		import from Z;
		st := newperm();
		setsign!(st, sign(s) * sign(t));
		for i in 1..n repeat st.i := s t i;
		st;
	}

	(s:%) ^ (m:Integer):% == {
		import from Z;
		zero? m => 1;
		one? m => s;
		m < 0 => inv(s)^(-m);
		sm := copy s;
		sgn:Z := { sign(s) > 0 or even? m => 1; -1 }
		setsign!(sm, sgn);
		for i in 2..m repeat sm := times!(sm, s);
		sm;
	}
	}
}

