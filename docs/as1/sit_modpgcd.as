------------------------------- sit_modpgcd.as --------------------------------
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"

macro {
	SI  == MachineInteger;
	ARR == PrimitiveArray;
}


ModulopUnivariateGcd: with {
	gcd!:(ARR SI, SI, ARR SI, SI, SI, SI) -> (ARR SI, SI, SI);
	gcd!:(ARR SI, SI, ARR SI, SI, SI, SI, ARR SI, ARR SI) -> (ARR SI,SI,SI);
} == add {
	local maxhalf:SI	== maxPrime$HalfWordSizePrimes;
	local maxint:SI		== max$SI;

#if ASTRACE
	local prt(str:String, a:ARR SI, n:SI, s:SI):() == {
		import from TextWriter, WriterManipulator;
		stderr << str << " = ";
		for i in 0..n repeat stderr << a(s+i) << " ";
		stderr << endnl;
	}
#else
	local prt(str:String, a:ARR SI, n:SI, s:SI):() == {};
#endif

	gcd!(a:ARR SI, n:SI, b:ARR SI, m:SI, lc:SI, p:SI):(ARR SI, SI, SI) == {
		import from String;
		TRACE("gcd!:p = ", p);
		prt("gcd!:a", a, n, 0);
		prt("gcd!:b", b, m, 0);
		assert(n >= m); assert(p > 1);
		p > maxhalf => fullgcd!(a, n, b, m, lc, p);
		-- from normalized inputs, the first k loops cannot overflow
		k := prev(maxint quo (prev(p) * prev(p)));
		TRACE("gcd!:k = ", k);
		k > 10 => halfgcd!(a, n, b, m, lc, k, p);
		halfgcd!(a, n, b, m, lc, p);
	}

	gcd!(a:ARR SI, n:SI, b:ARR SI, m:SI, lc:SI, p:SI, log:ARR SI,
		exp:ARR SI):(ARR SI, SI, SI) == {
			import from String;
			prt("gcd!:a", a, n, 0);
			prt("gcd!:b", b, m, 0);
			prt("gcd!:log", log, p-2, 0);
			prt("gcd!:exp", log, p-2, 0);
			assert(n >= m); assert(p > 1);
			gcd!(a, n, b, m, lc, p, log, exp, prev p);
	}

-- Those 3 files contain similar code with 3 different product functions
-- (the product is not passed as parameter because the function-call
--  overhead is too high, and this would prevent inlining)
#include "sit_fullgcd.as"
#include "sit_halfgcd.as"
#include "sit_loggcd.as"
}
