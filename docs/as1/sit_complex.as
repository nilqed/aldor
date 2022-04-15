--------------------------- sit_complex.as ----------------------------------
--
-- Extension of libaldor's Complex constructor
--
-- Copyright (c) Manuel Bronstein 2001
-- Copyright (c) INRIA 2001, Version 0.1.13
-- Logiciel Sum^it (c) INRIA 2001, dans sa version 0.1.13
-----------------------------------------------------------------------------

#include "algebra"
#include "algebrauid"


extend Complex(R:Join(ArithmeticType, ExpressionType)):
	LinearArithmeticType R with {
	if R has CharacteristicZero then CharacteristicZero;
	if R has CommutativeRing then CommutativeRing;
	if R has IntegralDomain then IntegralDomain;
	if R has Field then Field;
	if R has FiniteCharacteristic then FiniteCharacteristic;
	if R has FiniteField then FiniteField;
--	LATER WHEN (AND IF) NEEDED
--	if R has NonCommutativeIntegralDomain then NonCommutativeIntegralDomain;
	if R has Parsable then Parsable;
	if R has Ring then Algebra R;
	if R has RittRing then RittRing;
} == add {
	macro TREE == ExpressionTree;

	import from R;

	extree(a:%):TREE == {
		import from List TREE;
		t := extree real a;
		zero? imag a => t;
		ExpressionTreeComplex [t, extree imag a];
	}

	if R has Ring then {
		characteristic:Integer	== characteristic$R;
		coerce(n:Integer):%	== n::R::%;
		random():%		== complex(random(), random());

		(n: Integer) * (a: %): % == {
			zero? n => 0; one? n => a;
			complex(n * real a, n * imag a);
		}
	}

	if R has CommutativeRing then {
		-- this definition ought to work, but triggers an inliner bug.
	        reciprocal(a: %): Partial % == {
			import from Partial R;
		        l: Partial R := reciprocal(real(a) * real(a) + imag(a) * imag(a));
			failed? l => failed;
			tmp := retract l;
			[ complex(tmp * real a, tmp * (-imag(a)))]
		}
	}

	if R has IntegralDomain then {
		quotient(a:%, b:%):% == {
			import from Boolean;
			assert(~zero? b);
			zero? a or one? b => a;
			r := real a * real b + imag a * imag b;
			i := imag a * real b - real a * imag b;
			assert(zero? imag norm b);
			one?(d := real norm b) => complex(r, i);
			complex(quotient(r, d), quotient(i, d));
		}

		exactQuotient(a:%, b:%):Partial % == {
			import from Boolean, Partial R;
			assert(~zero? b);
			zero? a or one? b => [a];
			c := real a * real b + imag a * imag b;
			assert(zero? imag norm b);
			one?(d := real norm b) =>
				[complex(c, imag a * real b - real a * imag b)];
			failed?(u := exactQuotient(c, d)) => failed;
			c := imag a * real b - real a * imag b;
			failed?(v := exactQuotient(c, d)) => failed;
			[complex(retract u, retract v)];
		}
	}

	if R has Field then {
		inv(a:%):% == {
			import from Boolean;
			assert(~zero? a);
			one? a => a;
			assert(zero? imag norm a);
			one?(d := real norm a) => conjugate a;
			complex(real(a) / d, - imag(a) / d);
		}
	}

	if R has FiniteCharacteristic then {
		assert(characteristic$R > 2);	-- X^2+1 = (X+1)^2 otherwise

		local char3mod4?:Boolean == {
			import from Integer;
			~one?(characteristic$R mod 4);
		}

		pthPower(a:%):% == {
			zero? a or one? a => a;
			rp := pthPower real a;
			ip := pthPower imag a;
			if char3mod4? then ip := -ip;
			complex(rp, ip);
		}

		pthPower!(a:%):% == {
			zero? a or one? a => a;
			rp := pthPower real a;
			ip := pthPower imag a;
			if char3mod4? then ip := -ip;
			copy!(a, rp, ip);
		}
	}

	-- note that X^2+1 must be irreducible over R
	-- this is used in all the functions below
	if R has FiniteField then {
		degree:Integer	== 2;
		-- TEMPO: NEEDED BECAUSE #$% in lookup DOES NOT COMPILE
		local sz:Integer== (#$R) * (#$R);
		#:Integer	== sz;
		index(a:%):Integer == index(real a) + (#$R) * index(imag a);

		lookup(n:Integer):% == {
			m:Integer := n mod sz;
			(q, r) := divide(m, #$R);
			complex(lookup r, lookup q);
		}
	}

	if R has Parsable then {
		local float?:Boolean	== R has FloatType;
		local symbolimath:Symbol== { import from String; -"%i" }

		local floatdiv(a:%, b:%):(R, R, R) == {
			assert(zero? imag norm b);
			(real a * real b + imag a * imag b,
				imag a * real b - real a * imag b, real norm b);
		}

		eval(t:ExpressionTreeLeaf):Partial % == {
			import from Symbol, Partial R;
			symbol? t and symbol(t) = symbolimath => [complex(0,1)];
			failed?(u := eval(t)$R) => failed;
			[retract(u)::%];
		}

		eval(op:MachineInteger, args:List TREE):Partial % == {
			macro PC == (% pretend Join(Parsable, ArithmeticType));
			import from Boolean, Partial R, ParsingTools PC;
			~failed?(a := evalArith(op, args)) => a;
			op = UID__COMPLEX => {
				assert(#args = 2);
				failed?(u := eval(first args)$R) or
					failed?(v := eval(first rest args)$R) =>
									failed;
				[complex(retract u, retract v)];
			}
			R has FloatType and op = UID__DIVIDE => {
				assert(#args = 2);
				failed?(a := eval(first args)$PC) or
					failed?(b := eval(first rest args)$PC)=>
									failed;
				zero?(bb := retract b) => throw SyntaxException;
				zero?(aa := retract a) or one? bb => a;
				(r, i, d) := floatdiv(aa, bb);
				one? d => [complex(r, i)];
				[complex(r / d,	i / d)];
			}
			failed?(u := eval(op, args)$R) => failed;
			[retract(u)::%];
		}
	}
}

