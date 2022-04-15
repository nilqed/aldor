---------------------------- sit_modpoge.as ------------------------------------
-- Copyright (c) Thom Mulders 1996
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1996
-----------------------------------------------------------------------------
#include "algebra"
#include "aldorio"


macro {
	Z == MachineInteger;
	A == PrimitiveArray Z;
	M == PrimitiveArray A;
	-- GAMMA is an upper bound on the ratio (remainder/compare)
	-- for machine integers (actual value depend on hardware)
	GAMMA == 50;
}

ModulopGaussElimination: with {
	deter: (M, Z, A, Z, Z, Z) -> Z;
	determinant!: (M, Z, Z) -> Z;
	extendedRowEchelon!: (M, Z, Z, Z) -> (A, Z, A, Z, M);
	firstDependence!: (Generator A, Z, Z, M, M) -> Z;
	inverse!: (M, Z, Z, M, A) -> ();
	kernel!: (M, Z, Z, Z, M) -> Z;
	maxInvertibleSubmatrix!: (M, Z, Z, Z) -> (Array Z, Array Z);
	particularSolution!: (M, Z, Z, M, Z, Z, M, A) -> ();
	rank!: (M, Z, Z, Z) -> Z;
	rowEchelon!: (M, Z, Z, Z) -> (A, Z, A, Z);
	solve!: (M, Z, Z, M, Z, Z, M, A, M) -> Z;
	span!: (M, Z, Z, Z) -> Array Z;
} == add {
	local maxhalf:Z == maxPrime$HalfWordSizePrimes;
	local maxint:Z	== max$Z;

#if TRACE
	local prt(str:String, a:A, n:Z):() == {
		import from TextWriter, WriterManipulator;
		stderr << str;
		for i in 0..prev n repeat stderr << a.i << " ";
		stderr << endnl;
	}

	local prt(str:String, a:M, r:Z, c:Z):() == {
		import from TextWriter, WriterManipulator;
		stderr << str << " = ";
		for i in 0..prev r repeat prt("", a.i, c);
		stderr << endnl;
	}
#else
	local prt(str:String, a:A, n:Z):()	== {};
	local prt(str:String, a:M, r:Z, c:Z):() == {};
#endif

	rank!(a:M, ra:Z, ca:Z, p:Z):Z == {
		(pp,r,st,d) := rowEchelon!(a, ra, ca, p);
		r;
	}

	span!(a:M, ra:Z, ca:Z, p:Z):Array Z == {
		(pp,r,st,d) := rowEchelon!(a, ra, ca, p);
		array(st, r);
	}

	maxInvertibleSubmatrix!(a:M, ra:Z, ca:Z, p:Z):(Array Z, Array Z) == {
		import from A;
		(pp,r,st,d) := rowEchelon!(a, ra, ca, p);
		([next pp i for i in 0..prev r], array(st, r));
	}

	determinant!(a:M, n:Z, p:Z):Z == {
		(pp, r, st, d) := rowEchelon!(a, n, n, p);
		deter(a, n, pp, r, d, p);
	}

	rowEchelon!(a:M, ra:Z, ca:Z, p:Z):(A, Z, A, Z) == {
		import from String;
		prt("modpge::rowEchelon!: a", a, ra, ca);
		TRACE("modpge::rowEchelon!: p = ", p);
		rowEch!(a, ra, ca, empty, ra, 0, p);
	}

	extendedRowEchelon!(a:M, ra:Z, ca:Z, p:Z):(A, Z, A, Z, M) == {
		b:M := new ra;
		for i in 1..ra repeat {
			b.i := new(ra, 0);
			b.i.i := 1;
		}
		(pp, r, st, d) := rowEch!(a, ra, ca, b, ra, ra, p);
		(pp, r, st, d, b);
	}

	firstDependence!(gen:Generator A, n:Z, p:Z, work:M, sol:M):Z == {
		(sigma, r) := dependence(gen, n, p, work);
		assert(r <= next n);
		st:A := new(r1 := prev r);
		for i in 0..prev r1 repeat st.i := i;
		backSolve!(work, n, r, sol, 0, sigma, st, r1, r, p);
		r;
	}

	local dependence(gen:Generator A, n:Z, p:Z, work:M):(A, Z) == {
		assert(n > 0); assert(p > 1);
		p > maxhalf => fullDep(gen, n, p, work);
		halfDep(gen, n, p, work);
	}

	deter(a:M, n:Z, pp:A, r:Z, d:Z, p:Z):Z == {
		import from String;
		prt("modpge::deter:a", a, n, n);
		prt("modpge::deter:pp", pp, n);
		TRACE("modpge::deter:n = ", n);
		TRACE("modpge::deter:r = ", r);
		TRACE("modpge::deter:d = ", d);
		TRACE("modpge::deter: p = ", p);
		assert(p > 1);
		p > maxhalf => fullDeter(a, n, pp, r, d, p);
		halfDeter(a, n, pp, r, d, p);
	}

	-- stores the solutions in the matrix sol
	-- and returns the dimension of the kernel
	kernel!(a:M, n:Z, m:Z, p:Z, sol:M):Z == {
		import from A;
		(sigma, r, st, d) := rowEchelon!(a, n, m, p);
		nullSpace!(a, n, m, sol, sigma, r, st, p);
	}

	-- stores the solutions in the matrix sol
	-- and returns the dimension of the kernel
	local nullSpace!(a:M, n:Z, m:Z, sol:M, sigma:A, r:Z, st:A, p:Z):Z == {
		import from String;
		prt("modpge::nullSpace:a", a, n, m);
		prt("modpge::nullSpace:sigma = ", sigma, n);
		prt("modpge::nullSpace:st = ", st, r);
		TRACE("modpge::nullSpace:r = ", r);
		zero? r => {	-- kernel is an mxm identity matrix
			for i in 0..prev m repeat {
				for j in 0..prev m repeat sol.i.j := 0;
				sol.i.i := 1;
			}
			m;
		}
		k:Z := 0;
		for j in 1..st.0 repeat {
			backSolve!(a, n, m, sol, k, sigma, st, 0, j, p);
			k := next k;
		}
		for i in 1..prev r repeat {
			for j in next next(st(prev i))..st.i repeat {
				backSolve!(a, n, m, sol, k, sigma, st, i, j, p);
				k := next k;
			}
		}
		if r > 0 then for j in next next(st prev r)..m repeat {
				backSolve!(a, n, m, sol, k, sigma, st, r, j, p);
				k := next k;
		}
		k;
	}

	-- stores the solution in the matrix sol and the denoms in den
	inverse!(a:M, n:Z, p:Z, sol:M, den:A):() == {
		(sigma, r, st, d, b) := extendedRowEchelon!(a, n, n, p);
		backSolve!(a, n, n, sol, den, sigma, st, r, b, n, p);
	}

	-- stores a particular solution in the matrix sol, its denoms in den,
	-- a basis of the kernel in ker, and returns the dimension of the kernel
	-- the number of rows of b must be ra
	solve!(a:M, na:Z, ma:Z, b:M, mb:Z, p:Z, sol:M, den:A, ker:M):Z == {
		(sigma, r, st, d) := rowEch!(a, na, ma, b, na, mb, p);
		backSolve!(a, na, ma, sol, den, sigma, st, r, b, mb, p);
		nullSpace!(a, na, ma, ker, sigma, r, st, p);
	}

	-- stores the solution in the matrix sol and the denoms in den
	-- the number of rows of b must be ra
	particularSolution!(a:M, na:Z, ma:Z, b:M, mb:Z, p:Z, sol:M, den:A):()=={
		(sigma, r, st, d) := rowEch!(a, na, mb, b, na, mb, p);
		backSolve!(a, na, ma, sol, den, sigma, st, r, b, mb, p);
	}

	-- stores the solution in column k of the matrix sol
	-- c = column number is 1-indexed (first column is c = 1)
	local backSolve!(a:M,ra:Z,m:Z,sol:M,k:Z,sigma:A,st:A,r:Z,c:Z,p:Z):()=={
		p > maxhalf => fullBS!(a, ra, m, sol, k, sigma, st, r, c, p);
		halfBS!(a, ra, m, sol, k, sigma, st, r, c, p);
	}

	-- stores the solution in the matrix sol and the denoms in den
	-- the number of rows of b must be ra
	local backSolve!(a:M, ra:Z, ca:Z, sol:M, den:A,
				sigma:A, st:A, r:Z, b:M, cb:Z, p:Z):() == {
		p > maxhalf => fullBS!(a, ra, ca, sol, den, sigma, st,r,b,cb,p);
		halfBS!(a, ra, ca, sol, den, sigma, st, r, b, cb, p);
	}

	local rowEch!(a:M, ra:Z, ca:Z, b:M, rb:Z, cb:Z, p:Z):(A,Z,A,Z) == {
		import from String;
		prt("modpge::rowEch!: a", a, ra, ca);
		TRACE("modpge::rowEch!: p = ", p);
		assert(ra = rb); assert(p > 1);
		p > maxhalf => fullRowEch!(a, ra, ca, b, rb, cb, p);
		-- from normalized inputs, the first k loops cannot overflow
		k := prev(maxint quo (prev(p)*prev(p)));
		k > GAMMA or 4*k > ra => halfRowEch!(a, ra, ca, b, rb, cb, k,p);
		halfRowEch!(a, ra, ca, b, rb, cb, p);
	}

	local identity(n:Z):A == {
		assert(n > 0);
		a:A := new n;
		for i in 0..prev n repeat a.i := i;
		a;
	}

	local transpose!(p:A, i:Z, j:Z, d:Z):Z == {
		assert(i >= 0); assert(j >= 0);
		i = j => d;
		t := p.i;
		p.i := p.j;
		p.j := t;
		-d;
	}

-- Those 2 files contain similar code with 2 different product functions
-- (the product is not passed as parameter because the function-call
--  overhead is too high, and this would prevent inlining)
#include "sit_fullge.as"
#include "sit_halfge.as"
}

#if ALDORTEST

#include "algebra"
#include "aldorio"

macro {
	I == MachineInteger;
	Z == Integer;
	F == SmallPrimeField 3;
	M == DenseMatrix;
}

import from Symbol, I;

local bug():() == {
        import from Assert MachineInteger;
        import from Assert F;
	import from F, LinearAlgebra(F, M F);
	m:M F := zero(8,3);
	m(1,2) := 1;
	m(2,3) := 1;
	K := kernel m;
	assertEquals(3, numberOfRows K);
	assertEquals(1, numberOfColumns K);
	assertEquals(1, K(1,1));
	assertEquals(0, K(2,1));
	assertEquals(0, K(3,1));
}

bug();

local test(r: Z, c: Z, p: I): () == {
        import from Assert MachineInteger;
	Fp ==> SmallPrimeField p;
        import from Assert Fp;
	import from Vector Fp;
	import from Fp, LinearAlgebra(Fp, M Fp);
	for j in 1..10@Z repeat {
		m: M Fp := random(5,5);
		K := kernel m;
                (nrk, nck) := dimensions K;
	        for i in 1..10@Z repeat {
			v: M Fp := random(nck, 1);
			assertTrue(zero?(m * (K * v)));
	        }
       }
}

tt(): () == {
      import from AldorInteger;
      test(5,5,3::I);
      test(10,10,3::I);
      test(7,8,3::I);

      test(5,5,19::I);
      test(10,10,19::I);
      test(7,8,19::I)
}
tt();

#endif
