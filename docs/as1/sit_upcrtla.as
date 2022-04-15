---------------------------- sit_upcrtla.as ---------------------------------
-- Copyright (c) Helene Prieto 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"


macro {
	I==MachineInteger;
	Z==Integer;
	A==PrimitiveArray;
}


UnivariatePolynomialCRTLinearAlgebra(F:IntegralDomain,
	UPF:UnivariatePolynomialAlgebra0 F,
	M:MatrixCategory UPF): with {
		degreeBound: M -> Z;
		determinant: M -> Partial UPF;
		determinant: (M, UPF) -> Partial UPF;
		determinant: (M, UPF, Z) -> Partial UPF;
		rank: M -> Partial I;
} == add {
	local fin?:Boolean == F has FiniteSet;

	rank(m:M):Partial I		== rank(m, degreeBound m);
	determinant(m:M):Partial UPF	== determinant(m, 1$UPF, degreeBound m);
	determinant(m:M, d:UPF):Partial UPF == determinant(m, d, degreeBound m);

	if F has FiniteSet then {
		-- fd = garanteed factor of det(m);
		-- B is such that deg(det(m)) <= B)
		determinant(m:M, fd:UPF, B:Z): Partial UPF == {
			import from Boolean;
			assert(~zero? fd);
			B := B - degree fd;
			B >= #$F => failed;
			[deter(m, fd, B)];
		}

		rank(m:M, B:Z):Partial I == {
			B >= #$F => failed;
			[rank0(m, B)];
		}
	}
	else {
		-- fd = garanteed factor of det(m);
		-- B is such that deg(det(m)) <= B)
		determinant(m:M,fd:UPF,B:Z): Partial UPF == {
			import from Boolean;
			assert(~zero? fd);
			[deter(m, fd, B - degree fd)];
		}

		rank(m:M, B:Z):Partial I == [rank0(m, B)];
	}

	local eval!(m:DenseMatrix F, mg:A A Generator F):() == {
		import from I, Generator F, A Generator F;
		(n,nc) := dimensions m;
		for i in 0..prev n repeat for j in 0..prev nc repeat
			m(next i, next j) := next!(mg.i.j);
	}

	local getGens(m:M):A A Generator F == {
		import from I, F, A Generator F, UPF;
		(n,nc) := dimensions m;
		mg: A A Generator F := new n;
		for i in 0..prev n repeat {
			mg.i := new nc;
			for j in 0..prev nc repeat
				mg.i.j := values(m(next i, next j), 0);
		}
		mg;
	}

	-- B is such that deg(det(m)/fd) <= B)
	local rank0(m:M, B:Z):I == {
		import from LinearAlgebra(F, DenseMatrix F);

		assert(B >= 0);
		(n,nc) := dimensions m;
		assert(n > 0); assert(nc > 0);
		mp: DenseMatrix F := zero(n,nc);
		mg := getGens m;

		rk: I := 0;
		maxrank := min(n, nc);

		for k in 0..B repeat {
			eval!(mp, mg);
			r := rank mp;
			r = maxrank => return r;
			if r > rk then rk := r;
		}
		rk;
	}

	-- fd = garanteed factor of det(m);
	-- B is such that deg(det(m)/fd) <= B)
	local deter(m:M, fd:UPF, B:Z): UPF == {
		import from Boolean, I, F, Partial F;
		import from LinearAlgebra(F, DenseMatrix F);

		assert(~zero? fd); assert(B >= 0);
		n := numberOfRows m;
		assert(n > 0); assert(n=numberOfColumns m);
		mp: DenseMatrix F := zero(n,n);
		mg := getGens m;

		N: UPF :=1;
		det: UPF :=0;
		firststep:=true;

		k:Z :=0;
		x := monom;
	
		while k <= B repeat {
			xk := k::F;
			p:UPF := x - xk::UPF;
			fdmod := fd xk;
			if ~zero? fdmod then {	-- must compute det mod x-k
				eval!(mp, mg);
				d := determinant mp;
				assert(~failed? exactQuotient(d, fdmod));
				d := quotient(d, fdmod);
				if firststep then det := d::UPF;
				else {	-- combine d/fdmod with previous values
					b := d - det(xk);
					assert(~failed? exactQuotient(b,N(xk)));
					b := quotient(b, N(xk));
					det := add!(det, b * N);
				}
			}
			firststep := false;
			N := times!(N, p);
			k := next k;
		}
		times!(det, fd);
	}

	degreeBound(m:M):Z == {
		import from UPF,I;
		b:Z := 0;
		(r, c) := dimensions m;
		for i in 1..r repeat {
			d:Z := 0;
			for j in 1..c | ~zero?(p := m(i, j)) repeat {
				dg := degree p;
				if dg > d then d := dg;
			}
			b:=b+d;
		}
		bcol := b;
		b := 0;
		for j in 1..c repeat {
			d:Z := 0;
			for i in 1..r | ~zero?(p := m(i, j)) repeat {
				dg := degree p;
				if dg > d then d := dg;
			}
			b:=b+d;
		}
		min(b, bcol);
	}
}

