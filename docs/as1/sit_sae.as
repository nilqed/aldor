----------------------------- sit_sae.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1996
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1996-97
-----------------------------------------------------------------------------

#include "algebra"

macro {
	Z == Integer;
	GEN == Generator;
	UPMOD == UnivariatePolynomialModSqfr(R, Rx, modulus, avar);
	UPC0 == UnivariatePolynomialAlgebra0(%);
}


SimpleAlgebraicExtension(R:IntegralDomain,
	Rx: UnivariatePolynomialAlgebra0 R,
	modulus:Rx,
	avar:Symbol==new()):SimpleAlgebraicExtensionCategory(R,Rx)==UPMOD add {
		knownIrreducible?:Boolean == true;
}



define SimpleAlgebraicExtensionCategory(R:IntegralDomain,
	Rx: UnivariatePolynomialAlgebra0 R): Category ==
	Join(IntegralDomain, UnivariatePolynomialQuotientSqfr(R, Rx)) with {
		if R has Field then Field;
		if R has Join(Field, FactorizationRing, CharacteristicZero) then
			FactorizationRing;
		if R has FiniteField then FiniteField;
		default {
		if R has Field then {
			inv(f:%):% == {
				import from Partial %;
				failed?(u :=  reciprocal f) =>
					throw ReducibleModulusException(Rx,
						definingPolynomial, lift f);
				retract u;
			}
		}

		if R has Join(Field,FactorizationRing,CharacteristicZero) then {
			factor(P:UPC0)(p:P):(%, Product P) == {
				factor(p)$InternalAlgebraicFactorizer(R,
					Rx, %, P);
			}
		}

		if R has FiniteField then {
			degree:Z == degree(definingPolynomial)$Rx;
		}
		}
}

-- WON'T COMPILE WITHIN THE DEFAULTS OF SimpleAlgebraicExtension (ALDOR 1.0 BUG)
-- REALLY ONLY WORKS WHEN E IS A SimpleAlgebraicExtensionCategory
local InternalAlgebraicFactorizer(R:Join(FactorizationRing, CharacteristicZero),
		RX: UnivariatePolynomialAlgebra0 R,
		E: Join(GcdDomain, UnivariatePolynomialQuotientSqfr(R, RX)),
		EX: UnivariatePolynomialAlgebra0 E): with {
	factor: EX -> (E, Product EX);
} == add {
	factor(p:EX):(E, Product EX) == {
		import from Partial E;
		prd:Product EX := 1;
		(c, prod) := squareFree p;
		for trm in prod repeat {
			(q, n) := trm;
			lcp:E := 1;
			for f in factors q repeat {
				prd := times!(prd, f, n);
				lcp := times!(lcp, leadingCoefficient f);
			}
			lcq := leadingCoefficient q;
			-- lcp can differ from lcoeff(q) only by a unit in E
			if lcp ~= lcq then {
				assert(~failed? exactQuotient(lcp, lcq));
				c := times!(c, quotient(lcq, lcp));
			}
		}
		(c, prd);
	}

	-- generates the irreducible factors of p, which must be squarefree
	local factors(p:EX):Generator EX == {
		import from Z, RX, Product RX, UnivariateFreeRing2(R, RX, E, EX);
		assert(~zero? p); assert(degree p > 0);
		assert(degree squareFreePart p = degree p);
		(e, ps, q) := goodPoint p;
		(c, prod) := (factor(RX)$R)(q);
		RX2EX := map(coerce$E);
		translate(gcd(ps, RX2EX fact f), e) for f in prod;
	}

	local fact(p:RX, n:Z):RX == { assert(one? n); p }

	-- given p squarefree, returns (-e, p(x-e), norm(p(x-e)))
	-- where norm(p(x-e)) is squarefree
	-- guaranteed to terminate when E has characteristic 0
	local goodPoint(p:EX):(E, EX, RX) == {
		assert(~zero? p); assert(degree p > 0);
		norme := norm EX;
		s:Z := 0;
		q := norme p;
		zero? degree gcd(q, differentiate q) => (0, p, q);
		alpha:E := monom;
		repeat {
			s := next s;
			e := s * alpha;
			ps := translate(p, e);
			q := norme ps;
			zero? degree gcd(q, differentiate q) => return(-e,ps,q);
			e := -e;
			ps := translate(p, e);
			q := norme ps;
			zero? degree gcd(q, differentiate q) => return(-e,ps,q);
		}
	}
}
