----------------------------- sit_sercat.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"

macro {
	I == MachineInteger;
	Z == Integer;
	V == Vector;
	M == DenseMatrix;
	UPC == UnivariatePolynomialAlgebra;
	PR == DenseUnivariatePolynomial R;
	PC == % pretend UnivariateTaylorSeriesType R;
}


define UnivariateTaylorSeriesType(R:Join(ArithmeticType, ExpressionType)):
	Category == UnivariateFreeLinearArithmeticType R with {
		degree: % -> Partial Z;
		dot: V R -> V % -> %;
		finite?: % -> Boolean;
		if R has CommutativeRing then {
			differentiate: % -> %;
			differentiate: (%, Integer) -> %;
			if R has RittRing then {
				integrate: % -> %;
				integrate: (%, Integer) -> %;
			}
			reciprocal: % -> Partial %;
		}
		if R has FloatType then {
			reciprocal: % -> Partial %;
		}
		series: Sequence R -> %;
		default {
			if R has CommutativeRing then {
				if R has RittRing then {
					integrate(s:%):% == {
						import from Z;
						integrate(s, 1);
					}
				}

				differentiate(s:%):% == {
					import from Z;
					differentiate(s, 1);
				}

				local recipComring(s:%):Partial % == {
					import from Z, R, Partial R;
					s0 := coefficient(s, 0);
					failed?(u := reciprocal s0) => failed;
					[recip(s, retract u)];
				}
			}

			if R has FloatType then {
				local recipFloat(s:%):Partial % == {
					import from Z, R;
					zero?(s0 := coefficient(s,0)) => failed;
					[recip(s, 1 / s0)];
				}
			}

			-- REQUIRED BECAUSE COMPILER DOES NOT ACCEPT
			-- 2 SEPARATE CONDITIONAL DEFS FOR reciprocal
			-- local comring?:Boolean == R has CommutativeRing;
			-- local float?:Boolean	== R has FloatType;
			reciprocal(s:%):Partial % == {
				-- TEMPORARY: WOULD LIKE TO CACHE THE TESTS
				-- comring? => recipComring s;
				R has CommutativeRing => recipComring s;
				-- float? => recipFloat s;
				R has FloatType => recipFloat s;
				never;
			}

			-- computes s^{-1} given that s0 t0 = 1
			local recip(s:%, t0:R):% == {
				import from Stream R, Sequence R;
				series sequence [recipGen(s, t0)];
			}

			-- PROBABLY CAUSES TROUBLE IN CHARACTERISTIC 2
			-- computes s^{-1} via Newton given that s0 t0 = 1
			-- the usual iteration is t_{n+1} = 2t_n - s t_n^2
			-- to use + rather than -, we store g_n = -t_n, and
			-- the iteration becomes g_{n+1} = s g_n^2 + 2 g_n
			-- we must then yield the coefficients of -g
			local recipGen(s:%, t0:R):Generator R == generate {
				import from Z, PR,
				   UnivariateTaylorSeriesType2Poly(R,PC,PR);
				yield t0;
				g := (-t0)::PR;
				n:Z := 1;	-- s g = -1 mod x^n
				two:R := 1+1;
				repeat {
					m := 2 * n;
					sg2 := truncate!(truncate(s,m) * g^2,m);
					g := add!(sg2, two, g);
					for i in n..prev m repeat
						yield(- coefficient(g, i));
					n := m;
				}
			}

			(s:%)^(n:I):% == {
				import from BinaryPowering(%, I);
				binaryExponentiation(s, n);
			}
		}
}


UnivariateTaylorSeriesType2Poly(R:Join(ArithmeticType, ExpressionType),
	RXX: UnivariateTaylorSeriesType R,
	RX: UnivariatePolynomialAlgebra0 R): with {
		expand: R -> RX -> RXX;
		if R has Field then {
			expandFraction:R -> Fraction RX -> (Z,RXX);
		}
		if R has FloatType then {
			expandFraction: R -> Fraction RX -> (Z, RXX);
		}
		if R has IntegralDomain then {
			polynomials: (V RXX, Z) -> (V RX, M R);
			polynomials: (V RXX, Z, Z) -> (V RX, M R);
		}
		if R has CommutativeRing then {
			monicNewtonSeries: RX -> RXX;
			tryExpandFraction: R -> (RX, RX) -> (Z, Partial RXX);
		}
		truncate: (RXX, Z) -> RX;
} == add {
	expand(a:R):RX -> RXX == {
		f := coeffs a;
		(p:RX):RXX +-> {
			import from I, Z, R, Sequence R, Stream R;
			zero? p => 0;
			series sequence stream(f p, next machine degree p, 0);
		}
	}

	if R has CommutativeRing then {
		monicNewtonSeries(p:RX):RXX == {
			import from Z, R, RX, Partial RXX;
			assert(~zero? p);
			assert(unit? leadingCoefficient p);
			p := shift(p, -trailingDegree p);
			zero?(pp := differentiate p) => 0;
			d := prev(degree p - degree pp);
			assert(d >= 0);         -- always 0 in characteristic 0
			(nu, s) := tryExpandFraction(0)(shift!(revert! pp, d),
							revert p);
			assert(zero? nu);
			retract s;
		}

		tryExpandFraction(a:R):(RX, RX) -> (Z, Partial RXX) == {
			import from RX, RXX, Partial RXX;
			phi := expand a;
			nu := orderquo(monom - a::RX);
			(p:RX, q:RX):(Z, Partial RXX) +-> {
				assert(~zero? q);
				zero? p => (0, [0]);
				(d, den) := nu q;
				failed?(u := reciprocal phi den) => (-d,failed);
				(-d, [phi(p) * retract u]);
			}
		}
	}

	if R has Field then {
		expandFraction(a:R):Fraction RX -> (Z, RXX) == {
			import from RX, RXX, Partial RXX;
			phi := expand a;
			nu := orderquo(monom - a::RX);
			(f:Fraction RX):(Z, RXX) +-> {
				zero? f => (0, 0);
				(d, den) := nu denominator f;
				s := retract reciprocal phi den;
				(-d, phi(numerator f) * s);
			}
		}
	}

	if R has FloatType then {
		expandFraction(a:R):Fraction RX -> (Z, RXX) == {
			import from RX, RXX, Partial RXX;
			phi := expand a;
			nu := orderquo(monom - a::RX);
			(f:Fraction RX):(Z, RXX) +-> {
				zero? f => (0, 0);
				(d, den) := nu denominator f;
				s := retract reciprocal phi den;
				(-d, phi(numerator f) * s);
			}
		}
	}

	local coeffs(a:R):RX -> Generator R == {
		zero? a => {
			(p:RX):Generator R +-> coefficients p;
		 }
		(p:RX):Generator R +-> generate {
			import from Boolean, I, Z;
			assert(~zero? p);
			for i in 0..machine degree p repeat {
				(p, c) := Horner(p, a);
				yield c;
			}
		}
	}

	truncate(s:RXX, m:Z):RX == {
		assert(m >= 0);
		p:RX := 0;
		for i in prev(m)..0 by -1 repeat
			p := add!(p, coefficient(s, i), i);
		p;
	}

	if R has IntegralDomain then {

		dot(v:V RXX, m:M R):V RXX == {
			import from RXX;
			[dot(w)(v) for w in columns m];
		}

		polynomials(s:V RXX, degbound:Z):(V RX, M R) ==
			polynomials(s, degbound, -1);

		-- limit < 0 means no limit known, use heuristic
		-- otherwise make the series 0 from x^degbound+1 to x^limit
		polynomials(s:V RXX, degbound:Z, limit:Z):(V RX, M R) == {
			import from I, R, RXX;
			import from LinearAlgebra(R, M(R));
			assert(degbound >= -1);
			assert(limit < 0 or limit >= degbound);
			c := #s;
			r := { limit < 0 => c; machine(limit - degbound); }
			m:M R := zero(r, c);
			for i in r..1 by -1 repeat for j in 1..c repeat
				m(i, j) := coefficient(s.j, degbound + i::Z);
			dim := numberOfColumns(kern := kernel m);
			s := dot(s, kern);
			b := degbound + r::Z;	-- s = 0 from x^{bound+1} to x^b
			limit >= 0 =>
				([truncate(f, next degbound) for f in s], kern);
			-- Use heuristic refinement until dim=0 or dim unchanged
			non0? := true;
			while dim > 0 and non0? repeat {
				non0? := false;
				m := zero(dim, dim);
				for i in dim..1 by -1 repeat
					for j in 1..dim repeat {
						mij := coefficient(s.j, b+i::Z);
						m(i, j) := mij;
						if ~(non0? or zero? mij) then
							non0? := true;
				}
				if non0? then {
					dim:= numberOfColumns(newk := kernel m);
					kern := {
						dim > 0 => kern * newk;
						zero(0, 0);
					}
					s := dot(s, newk);
				}
				b := b + dim::Z;
			}
			([truncate(f, next degbound) for f in s], kern);
		}
	}
}

