----------------------------- sit_chrem.as ------------------------------------
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "algebra"

macro SI == MachineInteger;


ChineseRemaindering(R:EuclideanDomain): with {
	combine:	(R,R) -> (R,R) -> R;
	if R has IntegerType then {
		combine: (R, SI) -> (R, SI) -> R;
	}
	interpolate:	(List R,List R)	->	R;
} == add {
	local mustBalance?:Boolean	== R has IntegerType;
	local maxhalf:SI		== shift(1, prev(4 * bytes$SI));

	combine(M:R, m:R):(R,R) -> R == {
		import from Integer, Partial R;
		TRACE("computing inverse of ", M rem m);
		TRACE("modulo ",m);
		s := retract diophantine(M rem m, 1, m);
		mover2:R := { mustBalance? => m quo (2::R); 0 };
		TRACE("result=",s);
		(A:R, a:R):R +-> {
			b := (s * (a - (A rem m))) rem m;
			-- the following is only for integer-like rings
			if mustBalance? and greater?(b, mover2) then b := b - m;
			A + b * M;
		}
	}

	if R has IntegerType then {
		local greater?(a:R, b:R):Boolean == a > b;

		combine(M:R, m:SI):(R,SI) -> R == {
			import from Integer;
			assert(M > 0); assert(m > 0); assert(odd? m);
			mover2 := shift(m, -1);
			s := modInverse(M mod m, m);
			m > maxhalf => {
				(A:R, a:SI):R +-> {
					-- all args to mod_X must be positive!
					if a < 0 then a := a + m;
					aminusA := mod_-(a, A mod m, m);
					b := mod_*(s, aminusA, m);
					-- balance out result
					if b > mover2 then b := b - m;
					A + (b::R) * M;
				}
			}
			(A:R, a:SI):R +-> {
				-- all args to mod_X must be positive!
				if a < 0 then a := a + m;
				aminusA := mod_-(a, A mod m, m);
				b := (s * aminusA) rem m;
				-- balance out result
				if b > mover2 then b := b - m;
				A + (b::R) * M;
			}
		}
	}

	interpolate(p:List R, m:List R):R == {
		import from SI;
		assert(#p=#m);
		assert(#p>0);
		a := first p; p := rest p;
		M := first m; m := rest m;
		while ~empty? p repeat {
			np := first p; p := rest p;
			nm := first m; m := rest m;
			a  := combine(M, nm)(a, np);
			M  := nm * M;
		}
		a;
	}
}

#if ALDORTEST
------------------ test chrem.as -----------------
#include "algebra"
#include "aldortest"

macro {
	Z == Integer;
	F == SmallPrimeField 11;
	P == DenseUnivariatePolynomial F;
}

local inttest():Boolean == {
	import from Z, List Z, ChineseRemaindering Z;

	a := interpolate([4551,4671],[7927,7919]);
	a = 123456 => true;
	false;
}

local polytest():Boolean == {
	import from MachineInteger, Z, P, ChineseRemaindering P, List P;

	x := monom;
	a := interpolate([6*1,0,7*1],[x-1,x-2*1,x-3*1]);
	a = x*x+2*x+3*1 => true;
	false;
}

stdout << "Testing sit_chrem..." << endnl;
aldorTest("CRT for integers",inttest);
aldorTest("CRT for polynomials",polytest);
stdout << endnl;
#endif
