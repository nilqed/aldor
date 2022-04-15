---------------------------- sit_primgen.as ---------------------------------
--
-- Hard-coded primes of various machine-dependent sizes
--
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "algebra"


SmallPrimes: PrimeCollection == FixedPrimes PrimesSmall;


LazyHalfWordSizePrimes: PrimeCollection == FixedPrimes2(Primes13, Primes27);


HalfWordSizePrimes: PrimeCollection == FixedPrimes2(Primes15, Primes31);


WordSizePrimes: PrimeCollection == FixedPrimes2(Primes31, Primes63);
