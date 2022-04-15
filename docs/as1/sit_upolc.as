----------------------------- sit_upolc.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "algebra"

macro {
	I == MachineInteger;
	Z == Integer;
	UPC0 == UnivariatePolynomialAlgebra0 %;
	FR == FractionalRoot;
	RR == FR Z;
	RES == Resultant(R, %);
	RESP == Resultant(% pretend GcdDomain, P);
	GN == Generator;
	FRR==FR(R);
	REC == Record(sigmaexp:Z, exponent:Z);
	MAT == MatrixCategory;
	V == Vector %;
	AI == Array I;
	ORBIT == Cross(%, List REC);
	FLA == FiniteFieldUnivariatePolynomialLinearAlgebra;
	GENMOD == GenericModularPolynomialGcdPackage(%, P);
}


define UnivariatePolynomialAlgebra(R:Join(ExpressionType, ArithmeticType)):
	Category == UnivariatePolynomialAlgebra0 R with {
        if R has CommutativeRing then ModularComputation;
	if R has FiniteField then LinearAlgebraRing;
	if R has FactorizationRing then {
		SourceOfPrimes;
		if R has Field then UnivariateGcdRing;
		factor: % -> (R, Product %);
		fractionalRoots: % -> GN FRR;
		roots: % -> GN FRR;
	}
	if R has RationalRootRing then {
		RationalRootRing;
		if R has GcdDomain then {
			dispersion: % -> Z;
			dispersion: (%, %) -> Z;
			integerDistances: % -> List Z;
			integerDistances: (%, %) -> List Z;
		}
		integerRoots: % -> Generator RR;
		rationalRoots: % -> Generator RR;
		minIntegerRoot: % -> Partial Z;
		maxIntegerRoot: % -> Partial Z;
		if R has GcdDomain then {
			universalBound: (%, %) -> List Cross(%, Z);
		}
	}
	default {
		local gcd?:Boolean == R has GcdDomain;

		if R has CommutativeRing then {
		    residueClassRing(p: %): ResidueClassRing(%, p) == {
			UnivariatePolynomialResidueClassRing(R,%,p);
		    }
		}
		if R has IntegralDomain then {
			resultant(p:%, q:%):R == resultant(p, q)$RES;
		}

		if R has FactorizationRing then {
			getPrime(): Partial(%) == [monom];
			prime?(x: %): Partial(Boolean) == {
			        local c: R; local p: Product(%);
				(c, p) := factor(x);
				import from I, Product(%);
				[one?(#p)];			
			}

			getPrimeOfSize(d: I):Partial(%) == {
				import from I, Z;
				one? d => getPrime();
				failed;
			}

			nextPrime(x:%):Partial(%) == {
				import from I, Z, R;
				not one? leadingCoefficient(x) => failed;
			 	not one? degree x => failed;
				p: % := x + 1;
				p = monom => failed;
				[p];
			}

			if R has Field then {
				gcdUP(P:UPC0)(p:P, q:P):P == {
					import from Partial P;
					failed?(u := modularGcd(p, q)$GENMOD) =>
						subResultantGcd(p, q)$RESP;
					retract u;
				}
			}
		}

		if R has FiniteField then {
			determinant(M:MAT %):M->% == determinant$FLA(R,%,M);
			inverse(M:MAT %):M -> (M, V)	== inverse$FLA(R,%,M);
			kernel(M:MAT %):M -> M		== kernel$FLA(R,%,M);
			rank(M:MAT %):M -> I		== rank$FLA(R,%,M);
			solve(M:MAT %):(M,M) -> (M,M,V)	== solve$FLA(R,%,M);
			span(M:MAT %):M -> AI		== span$FLA(R,%,M);

			linearDependence(g:Generator V, n:I):V ==
				linearDependence(g, n)$FLA(R,%,DenseMatrix %);

			particularSolution(M:MAT %):(M, M) -> (M, V) ==
				particularSolution$FLA(R, %, M);

			maxInvertibleSubmatrix(M:MAT %):M -> (AI, AI) ==
				maxInvertibleSubmatrix$FLA(R, %, M);
		}

		if R has GcdDomain then {
			local gcdproject(P:UPC0, p:P):% == {
				import from Z;
				assert(~zero? p);
				q:% := 0;
				for i in 0..degree p repeat
					q := gcd(q, project(P, p, i));
				q;
			}

-- TEMPORARY: WHEN algebraic extensions have good gcd algorithms
#if MULTIGCD
			gcd(l:List %):% == {
				import from MultiGcd(R, %);
				(g, lq) := multiGcd l;
				g;
			}

			gcdquo(l:List %):(%, List %) == {
				import from MultiGcd(R, %);
				multiGcd l;
			}
#endif

			local ugring?:Boolean	== R has UnivariateGcdRing;
			local field?:Boolean	== R has Field;
			local infCharp?:Boolean == R has FiniteCharacteristic
							and ~(R has FiniteSet);

			gcd(p:%, q:%):%	== {
				ugring? => ugGcd(p, q);
				field? => eucl(p, q);
				subResultantGcd(p, q)$RES;
			};

			-- destroys p and q
			gcd!(p:%, q:%):% == {
				ugring? => ugGcd!(p, q);
				field? => eucl!(p, q);
				subResultantGcd(p, q)$RES;
			}

			squareFree(p:%):(R, Product %) == {
				import from Integer,
					UnivariatePolynomialSquareFree(R, %);
				infCharp? => musser p;
				yun p;
			}

			if R has UnivariateGcdRing then {
				local ugGcd(p:%, q:%):% == {
					(gcdUP$R)(%)(p, q);
				}

				local ugGcd!(p:%, q:%):% == {
					(gcdUP!$R)(%)(p, q);
				}

				gcdquo(p:%, q:%):(%, %, %) == {
					(gcdquoUP$R)(%)(p, q);
				}
			}

			if R has Field then {
				local eucl(p:%, q:%):%	== monic euclid(p, q);
				local eucl!(p:%, q:%):%	== monic! euclid!(p, q);
			}
		}

		if R has FactorizationRing then {
			factor(p:%):(R, Product %)	== (factor(%)$R)(p);
			roots(p:%):GN FRR		== (roots(%)$R)(p);
			fractionalRoots(p:%):GN FRR== (fractionalRoots(%)$R)(p);
		}

		if R has RationalRootRing then {
			integerRoots(p:%):GN RR  == (integerRoots(%)$R)(p);
			rationalRoots(p:%):GN RR == (rationalRoots(%)$R)(p);
			minIntegerRoot(p:%):Partial Z == zselect(p, <$Z);
			maxIntegerRoot(p:%):Partial Z == zselect(p, >$Z);

			local zselect(p:%, f?: (Z, Z) -> Boolean):Partial Z == {
				import from Boolean, RR;
				assert(~zero? p);
				emp? := true;
				n:Z := 0;
				for r in integerRoots p repeat {
					m := integralValue r;
					if emp? or f?(m, n) then n := m;
					emp? := false;
				}
				emp? => failed;
				[n];
			}

			if R has GcdDomain then {
				dispersion(p:%):Z == disp integerDistances p;

				dispersion(p:%, q:%):Z ==
					disp integerDistances(p, q);

				local disp(l:List Z):Z == {
					empty? l => -1;
					m := first l;
					for n in rest l repeat
						if n > m then m := n;
					m < 0 => -1;
					m;
				}

				universalBound(a:%, b:%):List Cross(%, Z) == {
					import from Boolean, Z, List Z, R;
					assert(~zero? a); assert(~zero? b);
					u:List Cross(%, Z) := empty;
					l := [e for e in integerDistances(a,b)|_
						e >= 0];
					empty? l => u;
					spr := reverse! sort! l;
					lastm := next first spr;
					for m in spr repeat {
						assert(m >= 0);
						assert(m < lastm);
						bm := translate(b, (-m)::R);
						g := primitivePart gcd(a, bm);
						if degree g > 0 then {
							a := quotient(a, g);
							gm := translate(g,m::R);
							b := quotient(b, gm);
							u := cons((g, m), u);
						}
					}
					u;
				}
			}

			local roots(P:UPC0, p:P, f:% -> GN RR):GN RR ==
				f project(P, p);

			integerRoots(P:UPC0):P -> GN RR ==
				(p:P):GN(RR) +-> roots(P, p, integerRoots$%);

			rationalRoots(P:UPC0):P -> GN RR ==
				(p:P):GN(RR) +-> roots(P, p, rationalRoots$%);


			local project(P:UPC0, p:P):% == {
				import from Z;
				zero? p => 0;
				-- TEMPORARY: WOULD LIKE TO CACHE THE TEST
				-- gcd? => gcdproject(P, p);
				R has GcdDomain => gcdproject(P, p);
				q:% := 1;
				for i in 0..degree p repeat
					q := times!(q, project(P, p, i));
				q;
			}

			local project(P:UPC0, p:P, m:Z):% == {
				q:% := 0;
				for term in p repeat {
					(c, n) := term;
					q := add!(q, coefficient(c, m), n);
				}
				q;
			}
		}
	}
}
