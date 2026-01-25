-- ======================================================================
-- This code was written all or part by Dr. Manuel Bronstein from
-- Inria-CAFE project team. After his sudden death on June 6, 2005, Inria
-- decided to publish this code under the CeCILL open source license in
-- memory of Dr. Manuel Bronstein.
-- 
-- This software is governed by the CeCILL license under French law and
-- abiding by the rules of distribution of free software. You can use,
-- modify and/or redistribute the software under the terms of the CeCILL
-- license as circulated by CEA, CNRS and Inria at the following URL :
-- http://www.cecill.info/licences/Licence_CeCILL_V2-en.html
-- 
-- As a counterpart to the access to the source code and rights to copy,
-- modify and redistribute granted by the license, users are provided
-- only with a limited warranty and the software's author, the holder of
-- the economic rights, and the successive licensors have only limited
-- liability.
-- 
-- In this respect, the user's attention is drawn to the risks associated
-- with loading, using, modifying and/or developing or reproducing the
-- software by the user in light of its specific status of free software,
-- that may mean that it is complicated to manipulate, and that also
-- therefore means that it is reserved for developers and experienced
-- professionals having in-depth computer knowledge. Users are therefore
-- encouraged to load and test the software's suitability as regards
-- their requirements in conditions enabling the security of their
-- systems and/or data to be ensured and, more generally, to use and
-- operate it in the same conditions as regards security.
-- 
-- The fact that you are presently reading this means that you have had
-- knowledge of the CeCILL license and that you accept its terms.
-- ======================================================================
-- 
----------------------------- sal_random.as -------------------------------
--
-- This file provides random number generators
--
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-- Copyright (c) Manuel Bronstein 1994-98
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro Z == MachineInteger;

extend MachineInteger: with {} == add {
	random():% == randomInteger()$RandomNumberGenerator;
	-- TEMPORARY: BUG1220, random(n) bound early to never!
	random(n:Z):% == random();
}

#if ALDOC
\thistype{RandomNumberGenerator}
\History{Manuel Bronstein}{10/8/94}{created}
\History{Manuel Bronstein}{15/10/98}{moved from sumit to salli and adapted}
\History{Manuel Bronstein}{9/02/2000}{added 32-bit generators}
\Usage{import from \this}
\Descr{\this~provides independent pseudo-random number generators.}
\begin{exports}
\asexp{apply}: & \% $\to$ Z & generate a random number\\
\asexp{generator}: & \% $\to$ \astype{Generator} Z & generate random numbers\\
\asexp{max}: & \% $\to$ Z & largest number that can be generated\\
\asexp{min}: & \% $\to$ Z & smallest number that can be generated\\
\asexp{numberOfGenerators}: & Z & number of predefined generators\\
\asexp{randomGenerator}: & () $\to$ \% & get a generator\\
\asexp{randomGenerator}: & Z $\to$ \% & get a generator\\
\asexp{randomGenerator}: & (Z, Z) $\to$ \% & get a bounded generator\\
\asexp{randomGenerator}: & (Z, Z, Z) $\to$ \% & get a bounded generator\\
\asexp{randomInteger}: & () $\to$ Z & generate a random number\\
\asexp{seed}: & (\%, Z) $\to$ Z & set the seed\\
\end{exports}
\begin{aswhere}
Z &==& \astype{MachineInteger}\\
\end{aswhere}
#endif

RandomNumberGenerator: with {
	apply: % -> Z;
#if ALDOC
\aspage{apply}
\Usage{ \name~r\\ r() }
\Signature{\%}{\astype{MachineInteger}}
\Params{ {\em r} & \% & a pseudo-random number generator\\ }
\Retval{Returns a pseudo-random integer.}
#endif
	generator: % -> Generator Z;
#if ALDOC
\aspage{generator}
\Usage{ for n in r repeat \{ \dots \}\\ for n in \name~r repeat \{ \dots \} }
\Signature{\%}{\astype{Generator} \astype{MachineInteger}}
\Params{ {\em r} & \% & a pseudo-random number generator\\ }
\Descr{This functions allows a for-loop that generates infinitely many
pseudo-random numbers.}
\begin{asex}
The following code computes the number of tries it takes for
a random generator to generate a multiple of 10:
\begin{ttyout}
multiple10():MachineInteger == {
    r := randomGenerator();
    for n in r for tries in 1.. repeat {
		zero?(n rem 10) => return tries;
    }
    never;
}
\end{ttyout}
\end{asex}
#endif
	max: % -> Z;
	min: % -> Z;
#if ALDOC
\aspage{max,min}
\Usage{max~r\\min~r}
\Signature{\%}{\astype{MachineInteger}}
\Params{ {\em r} & \% & a pseudo-random number generator\\ }
\Retval{max(r) and min(r) return respectively the largest and smallest
random integers that r can generate.}
#endif
	numberOfGenerators: Z;
#if ALDOC
\aspage{numberOfGenerators}
\Usage{\name}
\Signature{}{\astype{MachineInteger}}
\Retval{Returns the number of independent generators provided.}
#endif
	randomGenerator: (n:Z == 0) -> %;
	randomGenerator: (Z, Z, n:Z == 0) -> %;
#if ALDOC
\aspage{randomGenerator}
\Usage{ \name()\\ \name~n\\ \name(a, b)\\ \name(a, b, n) }
\Signatures{
\name: () $\to$ \%\\
\name: \astype{MachineInteger} $\to$ \%\\
\name: (\astype{MachineInteger}, \astype{MachineInteger}) $\to$ \%\\
\name:
(\astype{MachineInteger}, \astype{MachineInteger}, \astype{MachineInteger})
$\to$ \%\\
}
\Params{
{\em a, b} & \astype{MachineInteger} & bounds for the generator\\
{\em n} & \astype{MachineInteger} & identifier for the generator (optional)\\
}
\Retval{
\name() returns a pseudo-random generator, while
\name(a, b) returns a pseudo-random number generator that
generates numbers between a and b inclusive.
If the optional argument n is given, then the $\sth{n}$ independent
generator is returned, which allows for several independent sources
of random numbers.}
\seealso{\asexp{numberOfGenerators}}
#endif
	randomInteger: () -> Z;
#if ALDOC
\aspage{randomInteger}
\Usage{\name()}
\Signature{()}{\astype{MachineInteger}}
\Retval{Returns a pseudo-random integer.}
#endif
	seed: (%, Z) -> Z;
#if ALDOC
\aspage{seed}
\Usage{\name(r, s)}
\Signature{(\%, \astype{MachineInteger})}{\%}
\Params{
{\em r} & \% & a pseudo-random number generator\\
{\em s} & \astype{MachineInteger} & a nonzero seed\\
}
\Descr{Sets the seed of r to s and returns s. This is useful when a
reproducible pseudo-random sequence is desired. If an unseeded
generator is called, then it seeds itself from the system clock
the first time it is used, so the sequence is not reproducible. Note that
setting the seed to 0 causes the generator to generate an infinite sequence
of 0.}
#endif
} == add {
	Rep == Record(modulus:Z, multiplier:Z, last:Z, min:Z, sz:Z);

	local b64?:Boolean == { import from Z; bytes = 8 }

	-- last = -1 indicates unitialized yet, so use time for seed
	-- The 32-bit moduli and multipliers are taken from:
	--  Fishman & Moore, An exhaustive analysis of multiplicative
	--         congruential random number generators with modulus 2^31 - 1,
	--         SIAM J.Sci.Stat.Computation 7 (1986), 24-45. 
	-- The 64-bit moduli and multipliers are taken from:
	-- Krian & Goyal, Random number generation and testing,
	--                MTN 1, No.1, Spring 1994, 32-37.
	local rand0:% == {
		import from Rep, Z;
		b64? =>per [999999999989, 427419669081, -1, 0, 999999999989];
		per [2147483647, 950706376, -1, 0, 2147483647];
	}

	local rand1:% == {
		import from Rep, Z;
		b64? =>per [999999999989, 745580037424, -1, 0, 999999999989];
		per [2147483647, 62089911, -1, 0, 2147483647];
	}

	numberOfGenerators:Z		== 2;
	randomGenerator(n:Z):%		== { odd? n => rand1; rand0; }
	randomInteger():Z		== rand0();
	seed(r:%, n:Z):Z		== setlast!(r, abs n);
	min(r:%):Z			== { import from Rep; rep(r).min; }
	max(r:%):Z			== min(r) + prev size r;
	local last(r:%):Z		== { import from Rep; rep(r).last; }
	local mult(r:%):Z		== { import from Rep; rep(r).multiplier}
	local modulus(r:%):Z		== { import from Rep; rep(r).modulus; }
	local size(r:%):Z		== { import from Rep; rep(r).sz; }
	local setlast!(r:%, n:Z):Z	== { import from Rep; rep(r).last := n }
	local seeded?(r:%):Boolean	== { import from Z; last(r) >= 0; }
	generator(r:%):Generator Z	== generate { repeat yield r(); }

	apply(r:%):Z == {
		import { randomSeed: () -> Z } from Foreign C;
		x := { seeded? r => last r; abs randomSeed() }
		setlast!(r, mod_*(mult r, x, modulus r));
		min(r) + (last(r) rem size(r));
	}

	randomGenerator(a:Z, b:Z, n:Z):% == {
		import from Rep;
		r := rep randomGenerator n;
		per [r.modulus, r.multiplier, r.last, a, next(b - a)];
	}
}

#if SALLITEST
---------------------- test sal_random.as --------------------------
#include "sallitest"

macro I == MachineInteger;

local random():Boolean == { import from I; random 100; }

local random(m:I):Boolean == {
	import from Array I, RandomNumberGenerator;
	r := randomGenerator();
	seed(r, 1);
	a := new(m, 0);
	for n in r for i in 0..prev m repeat a.i := n;
	seed(r, 1);
	for i in 0..prev m repeat { a.i ~= r() => return false; }
	true;
}

stderr << "Testing sal__random..." << newline;
salliTest("random", random);
stderr << newline;
#endif

