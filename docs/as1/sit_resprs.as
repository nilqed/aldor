-------------------------- sit_resprs.as  ----------------------------
-- Copyright (c) Thom Mulders 1996
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1996-97
-----------------------------------------------------------------------------

#include "algebra"


Resultant(R:IntegralDomain,P:UnivariatePolynomialAlgebra0 R ): with {

	lastSPRS: (P,P) -> P;

	extendedLastSPRS: (P,P) -> (P,P,P);

	resultant: (P,P) -> R;

	SPRS: (P,P) -> List P;

	if R has GcdDomain then {
		subResultantGcd: (P,P) -> P;
	}

} == add {

-- See also: W.S. Brown: The subresultant PRS algorithm

	macro SI == MachineInteger;
	macro Z == Integer;

	import from SI,Z;

	-- degree a should be at least degree b
	local resultant!(a:P, b:P): R == {
		TRACE("resprs::resultant!: a = ", a);
		TRACE("resprs::resultant!: b = ", b);

		assert(~zero? a); assert(~zero? b);
		u1 := a; u2 := b;
		du1 := degree u1; du2 := degree u2;
		assert(du1 >= du2);
		zero? du1 => 1;		-- both a and b are nonzero constants
		delta := du1 - du2;
		h:R := 1;
		l:R := 1;
		cont?:Boolean := true;

		while cont? repeat {
			r := pseudoRemainder!(u1,u2);
			TRACE("resprs::resultant!: r = ", r);
			if (cont? := ~zero? r) then {
				{
					delta=0 => {};
					delta=1 => h := l;
					h := quotient(l^delta,h^(delta-1));
				}
				delta := degree u1 - degree u2;
				beta  := -l * (-h)^delta;
				u1 := u2;
				TRACE("resprs::resultant!: u1 = ", u1);
				l := leadingCoefficient u2;
				u2 := map( (x:R):R +-> quotient(x,beta)) r;
				TRACE("resprs::resultant!: u2 = ", u2);
			}
          	}
		degree u2 > 0 => 0;
		degree u1 = 1 => leadingCoefficient u2;
		assert(delta > 0);
		h := quotient(l^delta,h^(delta-1));
		delta := degree u1 -degree u2;
		l := leadingCoefficient u2;
		quotient(l^delta,h^(delta-1));
	}

	resultant(a:P,b:P): R == {
		import from Boolean;
		assert(~zero? a); assert(~zero? b);
		copya := copy a; copyb := copy b;
		da := degree a;
		db := degree b;
		da >= db => resultant!(copya, copyb);
		even? (da*db) => resultant!(copyb, copya);
		- resultant!(copyb, copya);
	}

	SPRS(a:P,b:P): List P == {
		assert(~zero? a); assert(~zero? b);

		import from R;

		list := [b,a];
		u1 := copy a; u2 := copy b;
		du1 := degree u1; du2 := degree u2;
		assert(du1 >= du2);
		delta := du1 - du2;
		h:R := 1;
		l:R := 1;
		cont?:Boolean := true;

		while cont? repeat {
			r := pseudoRemainder!(u1,u2);
			if (cont? := ~zero? r) then {
				{
					delta=0 => {};
					delta=1 => h := l;
					h := quotient(l^delta,h^(delta-1));
				}
				delta := degree u1 - degree u2;
				beta  := -l * (-h)^delta;
				u1 := u2;
				l := leadingCoefficient u2;
				u2 := map( (x:R):R +-> quotient(x,beta)) r;
				list := cons(copy u2,list);
			}
          	}

		list;
	}

	if R has GcdDomain then {
		subResultantGcd(a:P,b:P):P == {
			import from R;
			zero? a => b; zero? b => a;
			(ca, a) := primitive a;
			(cb, b) := primitive b;
			g := {
				degree a >= degree b => lastSPRS(a, b);
				lastSPRS(b, a);
			}
			gcd(ca, cb) * primitivePart g;
		}
	}

	lastSPRS(a:P,b:P): P == {

		assert(~zero? a); assert(~zero? b);

		import from R;

		u1 := copy a; u2 := copy b;
		du1 := degree u1; du2 := degree u2;
		assert(du1 >= du2);
		delta := du1 - du2;
		h:R := 1;
		l:R := 1;
		cont?:Boolean := true;

		while cont? repeat {
			r := pseudoRemainder!(u1,u2);
			if (cont? := ~zero? r) then {
				{
					delta=0 => {};
					delta=1 => h := l;
					h := quotient(l^delta,h^(delta-1));
				}
				delta := degree u1 - degree u2;
				beta  := -l * (-h)^delta;
				u1 := u2;
				l := leadingCoefficient u2;
				u2 := map( (x:R):R +-> quotient(x,beta)) r;
			}
          	}

		u2;

	}

	extendedLastSPRS(a:P,b:P): (P,P,P) == {

		assert(~zero? a); assert(~zero? b);

		import from R;
		u1 := copy a; u2 := copy b;
		du1 := degree u1; du2 := degree u2;
		assert(du1 >= du2);
		s1:P := 1; s2:P := 0;
		t1:P := 0; t2:P := 1;
		delta := du1 - du2;
		h:R := 1;
		l:R := 1;
		cont?:Boolean := true;

		while cont? repeat {
			(q,r) := pseudoDivide(u1,u2);
--print << u1 << newline << u2 <<newline << q << newline << r << newline << newline;
			if (cont? := ~zero? r) then {
				{
					delta=0 => {};
					delta=1 => h := l;
					h := quotient(l^delta,h^(delta-1));
				}
				delta := degree u1 - degree u2;
				beta  := -l * (-h)^delta;
				u1 := u2;
				l := leadingCoefficient u2;
				alpha := l^(delta+1);
				f := map( (x:R):R +-> quotient(x,beta) );
				s := f(alpha*s1-q*s2);
				s1 := s2; s2 := s;
				t := f(alpha*t1-q*t2);
				t1 := t2; t2 := t;
				u2 := f r;
			}
          	}

		(u2,s2,t2);

	}

}

