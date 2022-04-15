------------------------ sit_matquot.as ---------------------------
-- Copyright (c) Manuel Bronstein 1997
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Algebra (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1997
-----------------------------------------------------------------------------

#include "algebra"

macro {
	I == MachineInteger;
	Z == Integer;
	V == Vector;
}


define MatrixCategoryOverFraction(R:IntegralDomain, MR:MatrixCategory R,
	Q:FractionCategory R, MQ:MatrixCategory Q):
	LinearCombinationFraction(R, MR, Q, MQ) with {
		makeColIntegral: MQ -> (V R, MR);
		makeColIntegral: (MQ, I) -> (R, V R);
		makeRowIntegral: MQ -> (V R, MR);
		makeRowIntegral: (MQ, I) -> (R, V R);
		if Q has FractionByCategory0 R then {
			makeRowIntegralBy: MQ -> (V Z, MR);
		}
} == add {
	macro gcd? == R has GcdDomain;

	makeRowIntegral(B:MQ, r:I):(R, V R) == {
		import from VectorOverFraction(R, Q);
		makeIntegral row(B, r);
	}

	makeColIntegral(B:MQ, c:I):(R, V R) == {
		import from VectorOverFraction(R, Q);
		makeIntegral column(B, c);
	}

	-- Most of those functions use the fact that IntegralDomain's are
        -- commutative (if fractions of noncommutative domains are used
        -- one day, those functions must be recoded, as they will give
	-- incorrect results if R is not commutative).

	(x:Q) * (A:MR):MQ == {
		import from I;
		(r, c) := dimensions A;
		B:MQ := zero(r, c);
		for i in 1..r repeat for j in 1..c repeat B(i,j) := A(i,j) * x;
		B;
	}

	makeRational(A:MR):MQ == {
		import from I, Q;
		(r, c) := dimensions A;
		B:MQ := zero(r, c);
		for i in 1..r repeat for j in 1..c repeat B(i,j) := A(i,j)::Q;
		B;
	}

	if Q has FractionFieldCategory0 R then {
		normalize(A:MR):(R, MQ) == {
			import from I, Q;
			(r, c) := dimensions A;
			B:MQ := zero(r, c);
			zero? r or zero? c => (1, B);
			a := A(1, 1);
			for i in 1..r repeat for j in 1..c repeat
				B(i,j) := A(i,j) / a;
			(a, B);
		}
	}

	local prod(l:List R):R == {
		r:R := 1;
		while ~empty? l repeat {
			r := times!(r, first l);
			l := rest l;
		}
		r;
	}

	-- common denominator for col c
	local coldenom(B:MQ, c:I):R == {
		import from Q, List R;
		denoms := [denominator(B(i, c)) for i in 1..numberOfRows B];
		gcd? => lcm(denoms);
		prod denoms;
	}

	-- common denominator for row r
	local rowdenom(B:MQ, r:I):R == {
		import from Q, List R;
		denoms := [denominator(B(r, j)) for j in 1..numberOfColumns B];
		gcd? => lcm(denoms);
		prod denoms;
	}

	makeIntegral(B:MQ):(R, MR) == {
		import from I, R, Q, List R;
		(r, c) := dimensions B;
		denoms := [rowdenom(B, i) for i in 1..r];
		d := { gcd? => lcm(denoms); prod denoms; }
		A:MR := zero(r, c);
		for i in 1..r repeat for j in 1..c repeat
			A(i,j) := numerator(d * B(i,j));
		(d, A);
	}

	local makeRowIntegral!(A:MR, v:V R, B:MQ, r:I):() == {
		import from I, Q;
		c := numberOfColumns B;
		assert(c <= numberOfColumns A);
		assert(r > 0); assert(r <= numberOfRows A);
		v.r := rowdenom(B, r);
		for j in 1..c repeat A(r, j) := numerator(v.r * B(r, j));
	}

	makeRowIntegral(B:MQ):(V R, MR) == {
		import from I, V R;
		(r, c) := dimensions B;
		A:MR := zero(r, c);
		v:V R := zero r;
		for i in 1..r repeat makeRowIntegral!(A, v, B, i);
		(v, A);
	}

	local makeColIntegral!(A:MR, v:V R, B:MQ, c:I):() == {
		import from I, Q;
		r := numberOfRows B;
		assert(r <= numberOfRows A);
		assert(c > 0); assert(c <= numberOfColumns A);
		v.c := coldenom(B, c);
		for i in 1..r repeat A(i, c) := numerator(v.c * B(i, c));
	}

	makeColIntegral(B:MQ):(V R, MR) == {
		import from I, V R;
		(r, c) := dimensions B;
		A:MR := zero(r, c);
		v:V R := zero c;
		for j in 1..c repeat makeColIntegral!(A, v, B, j);
		(v, A);
	}

	if Q has FractionByCategory0 R then {
		-- returns mu s.t. p^(-mu) * row i is integral
		local order(B:MQ, r:I):Z == {
			import from Boolean, Q;
			mu:Z := 0;
			for j in 1..numberOfColumns B |~zero?(b:=B(r,j)) repeat{
				m:Z := order(b)$Q;
				if m < mu then mu := m;
			}
			assert(mu <= 0);
			mu;
		}

		local makeRowIntegral!(A:MR, v:V Z, B:MQ, r:I):() == {
			import from I, Z, Q;
			c := numberOfColumns B;
			assert(c <= numberOfColumns A);
			assert(r > 0); assert(r <= numberOfRows A);
			v.r := - order(B, r);
			for j in 1..c repeat
				A(r, j) := numerator shift(B(r, j), v.r);
		}

		makeRowIntegralBy(B:MQ):(V Z, MR) == {
			import from I, V Z;
			(r, c) := dimensions B;
			A:MR := zero(r, c);
			v:V Z := zero r;
			for i in 1..r repeat makeRowIntegral!(A, v, B, i);
			(v, A);
		}

		makeIntegralBy(B:MQ):(Z, MR) == {
			import from I, Z, Q;
			mu:Z := 0;
			(r, c) := dimensions B;
			for i in 1..r repeat {
				m := order(B, i);
				if m < mu then mu := m;
			}
			assert(mu <= 0);
			A:MR := zero(r, c);
			for i in 1..r repeat for j in 1..c repeat
				A(i, j) := numerator shift(B(i, j), -mu);
			(mu, A);
		}
	}
}
