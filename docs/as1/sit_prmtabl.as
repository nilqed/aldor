---------------------------- sit_prmtabl.as ---------------------------------
--
-- Interface to hard-coded tables of primes
--
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "algebra"

macro Z	== MachineInteger;

define PrimeTable: Category == with {
	primes: Array Z;	-- the actual primes
	fourier: Array Z;	-- fourier primes
	roots: Array Z;		-- either primitive roots for primes
				-- or primitive roots of 1 for fourier primes
};


define PrimeCollection: Category == with {
	allPrimes: () -> Generator Z;
	fourierPrime: Z -> (Z, Z);
	maxPrime: Z;
	nextPrime: Z -> Z;
	previousPrime: Z -> Z;
	primeInCollection?: Z -> Boolean;
	primRoot: Z -> Z;
	randomPrime: () -> Z;
}

FixedPrimes(T:PrimeTable): PrimeCollection == add {
	local primes:Array Z	== primes$T;
	local fourier:Array Z	== fourier$T;
	local roots:Array Z	== roots$T;
	local nprimes:Z		== #primes;
	local nfourier:Z	== #fourier;
	local prim?:Boolean	== nprimes = #roots;
	maxPrime:Z		== primes(prev nprimes);
	randomPrime():Z		== primes(random()$Z mod nprimes);
	allPrimes():Generator Z	== generator primes;

	fourierPrime(n:Z):(Z, Z) == {
		n < 1 or n > nfourier => (0, 0);
		(fourier(prev n), { prim? => 0; roots(prev n) });
	}

	nextPrime(n:Z):Z == {
		(found?, index) := search n;
		oddPrime next index;
	}

	primRoot(n:Z):Z == {
		prim? => {
			(found?, index) := search n;
			found? => roots.index;
			0;
		}
		0;
	}

	previousPrime(n:Z):Z == {
		(found?, index) := search n;
		found? => oddPrime prev index;
		-- TEMPORARY: WORK-AROUND to a SALLI 0.1.12e binarySearch BUG
		-- index >= nprimes => maxPrime;
		oddPrime index;
	}

	-- check bounds and returns 0 if out of bounds
	local oddPrime(index:Z):Z == {
		TRACE("oddPrime: ", index);
		index < 0 or index >= nprimes => 0;
		primes.index;
	}

	primeInCollection?(n:Z):Boolean == {
		(found?, index) := search n;
		found?;
	}

	-- return (found?, i) such that:
	--   if found? is true, then n = wordprimes.i
	--   if found? is false, then:
	--	if 0 <= i < nprimes-1, then wordprimes.i < n < wordprimes(i+1)
	--	if i = nprimes-1 then wordprimes(nprimes - 1) < n
	local search(n:Z):(Boolean, Z) == {
		import from Array Z;
		binarySearch(n, primes);
	}
}

-- select T32 or T64 depending on the word-size of the machine
FixedPrimes2(T32:PrimeTable, T64:PrimeTable): PrimeCollection == {
	import from Z;

	local w:Z == bytes;

	-- TEMPORARY: WORKAROUND FOR BUG1167
	-- w = 4 => FixedPrimes T32;
	w = 4 => FixedPrimes T32 add;
	assert(w = 8);
	-- TEMPORARY: WORKAROUND FOR BUG1167
	-- FixedPrimes T64;
	FixedPrimes T64 add;
}

