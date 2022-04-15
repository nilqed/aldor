----------------------------- sit_algext.as ---------------------------------
-- Copyright (c) Manuel Bronstein 1996
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1996-97
-----------------------------------------------------------------------------

#include "algebra"


macro {
	I	== MachineInteger;
	Z	== Integer;
	GEN	== Generator;
	ARR	== PrimitiveArray;
	UPC0	== UnivariatePolynomialAlgebra0;
	POLY	== UnivariatePolynomialAlgebra;
	Rxx	== DenseUnivariateTaylorSeries R;
}

define UnivariatePolynomialQuotient(R:CommutativeRing, Rx:UPC0 R):
	Category == Join(CommutativeRing, Algebra R) with {
		if R has FiniteSet then FiniteSet;
		if R has CharacteristicZero then CharacteristicZero;
		if R has FiniteCharacteristic then FiniteCharacteristic;
		coefficient: (%, Z) -> R;
		compose: % -> % -> %;
		definingPolynomial: Rx;
		generator: % -> GEN Cross(R, Z);
		knownIrreducible?: Boolean;
		lift: % -> Rx;
		map: (R -> R) -> % -> %;
		map!: (R -> R) -> % -> %;
		monom: %;
		reduce: Rx -> %;
		value: (P:UPC0 %) -> (P, Z, Z) -> %;
		default {
			monom:% == reduce(monom$Rx);

			if R has FiniteSet then {
				#:Z == {
					import from Rx;
					(#$R)^(degree definingPolynomial);
				}

				-- storing is by increasing degree:
				--  degree 0 = index$R
				--  degree 1 = #$R*index(coeff1) + index(coeff0)
				--  etc.
				index(x:%):Z == {
					import from R;
					p:Rx := lift x;
					zero? p => 0;
					r := #$R;
					assert(r > 0);
					v := index leadingCoefficient p;
					for i in prev degree p .. 0 by -1 repeat
						v := r*v+index coefficient(p,i);
					v;
				}

				lookup(n:Z):% == {
					import from R, Rx;
					m := n mod (#$%);
					assert(m >= 0);
					r := #$R;
					assert(r > 0);
					d := degree definingPolynomial;
					p := monomial d;
					i:Z := 0;
					while m > 0 repeat {
						(m, a) := divide(m, r);
						p := add!(p, lookup a, i);
						i := next i;
					}
					p := add!(p, -1, d);	-- remove x^d
					reduce p;
				}
			}

			-- returns d^{degree p} p(n/d)
			local qvalue(P:UPC0 %, p:P, n:Z, d:Z):% == {
				import from Boolean, R;
				assert(~unit?(d::R));
				v:% := 0;
				g := degree p;
				for term in p repeat {
					(c, e) := term;
					if ~(zero? c) then
						v := add!(v, n^e * d^(g-e) * c);
				}
				v;
			}

			value(P:UPC0 %):(P, Z, Z) -> % == {
				(p:P, n:Z, d:Z):% +-> {
					import from R, Partial R;
					u := reciprocal(d::R);
					failed? u => qvalue(P, p, n, d);
					d1 := retract u;
					p((n * d1)::%);
				}
			}
		}
}


define UnivariatePolynomialQuotientSqfr(R:CommutativeRing, Rx:UPC0 R):
	Category == UnivariatePolynomialQuotient(R, Rx) with {
		if R has RationalRootRing then RationalRootRing;
		if R has CharacteristicZero and R has Field then
							DifferentialExtension R;
		newtonSeries: Rxx;
		norm: % -> R;
		norm: (P:UPC0 %) -> P -> Rx;
		trace: % -> R;
		trace: (P:UPC0 %) -> P -> Rx;
	default {
		-- TEMPORARY: RUNTIME SEG FAULT ON definingPolynomial (1.0.0)
		-- newtonSeries:Rxx == monicNewtonSeries(definingPolynomial)$_
				UnivariateTaylorSeriesType2Poly(R, Rxx, Rx);

		if R has RationalRootRing then {
			macro IID == (% pretend IntegralDomain);
			macro RR == FractionalRoot Z;

			local intdom?:Boolean	== R has IntegralDomain;
			local gcddom?:Boolean	== R has GcdDomain;
			local fring?:Boolean	== R has FactorizationRing;

			local N1:MachineInteger ==
				prev(machine(degree(definingPolynomial)$Rx)$Z);

			-- takes only the coefficients of alpha^m
			local project(P:UPC0 %, p:P, m:Z):Rx == {
				q:Rx := 0;
				for term in p repeat {
					(c, n) := term;
					q := add!(q, coefficient(c, m), n);
				}
				q;
			}

			if R has GcdDomain then {
				-- returns the gcd of all the projections
				local gcdproject(P:UPC0 %, p:P):Rx == {
					import from Boolean, MachineInteger, Z;
					assert(~zero? p);
					q:Rx := 0;
					for i in 0..N1 repeat
						q := gcd(q, project(P,p,i::Z));
					q;
				}
			}

			local project(P:UPC0 %, p:P):Rx == {
				import from Z;
				assert(~zero? p);
				-- TEMPORARY: WOULD LIKE TO CACHE THE TEST
				-- gcddom? => gcdproject(P, p);
				R has GcdDomain => gcdproject(P, p);
				-- returns the first nonzero projection
				for i in 0..N1 repeat
					~zero?(q := project(P, p, i::Z)) =>
								return q;
				never;
			}

			integerRoots(P:UPC0 %):P -> GEN RR ==
				(p:P):GEN(RR) +-> roots(P,p,integerRoots(Rx)$R);

			rationalRoots(P:UPC0 %):P -> GEN RR ==
				(p:P):GEN(RR)+-> roots(P,p,rationalRoots(Rx)$R);

			local nroots(l:List RR):Z == {
				import from RR;
				n:Z := 0;
				for rt in l repeat n := add!(n,multiplicity rt);
				n;
			}

			local roots(P:UPC0 %, p:P, f:Rx -> GEN RR):GEN RR == {
				import from Z;
				assert(~zero? p);
				gen := f project(P, p);
				knownIrreducible? => {
					gcddom? => gen;
					checkroots(P, p, gen);
				}
				ll:List RR := [checkroots(P, p, gen)];
				nroots(ll) = degree p => generator ll;
			-- TEMPORARY: should deflate p with the known roots
				fring? => frroots(P, p, f, ll);
				f(norm(P)(normalize(P, p)));
			}

			local checkroots(P:UPC0 %, p:P, gen:GEN RR):GEN RR ==
				generate {
				import from Z, RR;
				assert(~zero? p);
				for r in gen repeat {
					(n, d) := value r;
					q:P := term(d::%, 1) - n::P;
					m := order(q)(p);
					if m > 0 then
						yield setMultiplicity!(r, m);
				}
			}

			-- reduces the coeffs of p modulo q and then projects
			local project(P:UPC0 %, p:P, q:Rx):Rx == {
				import from R, Partial R;
				assert(unit?(leadingCoefficient(q)$Rx));
				remq! := monicRemainderBy! q;
				pp:P := 0;
				for term in p repeat {
					(c, e) := term;
					pp := add!(pp, reduce remq! lift c, e);
				}
				project(P, pp);
			}

			-- make p monic if it is possible, return p otherwise
			local normalize(P:UPC0 %, p:P):P == {
				import from Partial %;
				zero? p => p;
				a := leadingCoefficient p;
				~failed?(u := reciprocal a) => retract(u) * p;
				~intdom? => p;
				q:P := monomial degree p;
				for term in reductum p repeat {
					(c, n) := term;
					failed?(u:= exactQuotient(c,a)$IID) =>
								return p;
					q := add!(q, retract u, n);
				}
				q;
			}

			if R has FactorizationRing then {
				local NFactors:ARR I == new(1$I, 0$I);

				local factModulus:ARR Rx ==
					new(machine(degree(
						definingPolynomial)$Rx)$Z);

				local factorModulus():I == {
					import from I,R,Rx, Product Rx, ARR Rx;
					assert(~knownIrreducible?);
					(c, prd) :=
						factor(Rx)(definingPolynomial);
					NFactors.0 := #prd;
					n := prev(NFactors.0);
					for t in prd for i in 0..n repeat {
						(q, e) := t;
						if zero? i then q := c * q;
						factModulus.i := q;
					}
					NFactors.0;
				}

				-- projects on all the factors
				local frroots(P:UPC0 %, p:P,
					f:Rx -> GEN RR, l:List RR):GEN RR == {
					import from I, ARR I, ARR Rx;
					if zero?(n := NFactors.0) then
						n := factorModulus();
					one? n => generator l;
					ll:List RR := empty;
					for i in 0..prev n repeat {
						ll := merge(ll, f project(P, p,
								factModulus.i));
					}
					generator ll;
				}

				local find(r:RR, l:List RR):Partial RR == {
					import from Z;
					(n, d) := value r;
					for rt in l repeat {
						(a, b) := value rt;
						a*d = b*n => return [rt];
					}
					failed;
				}

				local merge(l1:List RR, l2:GEN RR):List RR == {
					import from Z, RR;
					for t in l2 repeat {
						(l:List RR, ig:I) := find(t,l1);
						if empty? l then l1:=cons(t,l1);
						else {
							r := first l;
							assert(r = t);
							setMultiplicity!(r,
								multiplicity r +
								multiplicity t);
						}
					}
					l1;
				}
			}
		}
	}
}
