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
------------------------------- random.as ----------------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1994

#include "sumit"

#if ASDOC
\thistype{RandomNumberGenerator}
\History{Manuel Bronstein}{10/8/94}{created}
\Usage{import from \this}
\Descr{\this~provides independent pseudo-random number generators.}
\begin{exports}
apply: & \% $\to$ Z & get a random number from a generator\\
minmax: & \% $\to$ (Z, Z) &
range of numbers that can be generated\\
randomGenerator: & Z $\to$ \% & create a random number generator\\
randomGenerator: & (Z, Z, Z) $\to$ \% &
create a random number generator\\
randomInteger: & () $\to$ Z & get a random number\\
seed: & (\%, Z) $\to$ \% & set the seed\\
\end{exports}
\Aswhere{
Z &==& Integer\\
}
#endif

RandomNumberGenerator: BasicType with {
	apply: % -> Integer;
#if ASDOC
\begin{aspage}{apply}
\Usage{ \name~r\\ r() }
\Signature{\%}{Integer}
\Params{
{\em r} & \this & A pseudo-random number generator\\
}
\Retval{Returns a pseudo-random integer.}
\end{aspage}
#endif
	minmax: % -> (Integer, Integer);
#if ASDOC
\begin{aspage}{minmax}
\Usage{\name~r}
\Signature{\this}{(Integer, Integer)}
\Params{ {\em r} & \this & A pseudo-random number generator\\ }
\Retval{\name~r returns the smallest and largest pseudo-random integers that r
can generate.}
\end{aspage}
#endif
	randomGenerator: Integer -> %;
	randomGenerator: (Integer, Integer, Integer) -> %;
#if ASDOC
\begin{aspage}{randomGenerator}
\Usage{ \name~n\\ \name(n, a, b) }
\Signatures{
\name: Integer $\to$ \this\\
\name: (Integer, Integer, Integer) $\to$ \this\\
}
\Params{ {\em n} & Integer & The indentifier for the generator\\ }
\Retval{
\name~n returns the \Th{n} independent pseudo-random generator.\\
\name(n, a, b) returns a pseudo-random number generator based on the
\Th{n} independent generator, but which generates numbers between a and b
inclusive.\\
There are currently 2 independent generators available, so all those functions
really returns the \Th{(n~mod~2)} generator.
}
\end{aspage}
#endif
	randomInteger: () -> Integer;
#if ASDOC
\begin{aspage}{randomInteger}
\Usage{\name()}
\Signature{()}{Integer}
\Retval{\name() returns a pseudo-random integer using the first random
number generator.}
\end{aspage}
#endif
	seed: (%, Integer) -> %;
#if ASDOC
\begin{aspage}{seed}
\Usage{\name(r, n)}
\Signature{(\this, Integer)}{\this}
\Descr{\name(r,n) sets the seed $r$ to $n$, which is useful when a reproducible
pseudo-random sequence is desired. $n$ must be nonnegative.}
\Retval{Returns $r$.}
\end{aspage}
#endif
} == add {
	macro Z == Integer;
	macro Rep == Record(modulus:Z, multiplier:Z, increment: Z,
				last:Z, min:Z, sz:Z);

	import from Z, Rep;

	-- last = -1 indicates unitialized yet, so use time for seed
	rand1:%	== per [999999999989, 427419669081, 0, -1, 0, 999999999989];
	rand2:%	== per [999999999989, 745580037424, 0, -1, 0, 999999999989];

	sample:%			== rand1;
	randomGenerator(n:Integer):%	== { odd? n => rand1; rand2; }
	randomInteger():Integer		== rand1();

	seed(r:%, n:Integer):% == {
		ASSERT(n >= 0);
		rep(r).last := n;
		r;
	}

	(r:%) = (s:%):Boolean == {
		rr := rep r; rs := rep s;
		rr.modulus = rs.modulus and rr.multiplier = rs.multiplier
			and rr.increment = rs.increment
				and rr.min = rs.min and rr.sz = rs.sz;
	}

	(p:TextWriter) << (r:%):TextWriter == {
		rc := rep r;
		p << "randomGenerator(X_{i+1} = " << rc.multiplier << " X_i";
		if (rc.increment ~= 0) then p << " + " << rc.increment;
		p << " (mod " << rc.modulus << ")";
	}

	apply(r:%):Z == {
		import { randomSeed: () -> SingleInteger } from Foreign C;
		rc := rep r;
		x := { rc.last < 0 => abs(randomSeed()::Z); rc.last; }
		rc.last := (rc.multiplier * x + rc.increment) mod rc.modulus;
		x := { rc.last < rc.sz => rc.last; rc.last mod rc.sz; }
		x + rc.min;
	}

	minmax(r:%):(Z, Z) == {
		rc := rep(r);
		m := rc.min;
		(m, m + rc.sz - 1);
	}

	randomGenerator(n:Integer, a:Integer, b:Integer):% == {
		r := rep randomGenerator n;
		per [r.modulus, r.multiplier, r.increment, r.last, a, b-a+1];
	}
}

#if SUMITTEST
---------------------- test random.as --------------------------
#include "sumittest.as"

random():Boolean == {
	import from SingleInteger,Integer,Array Integer,RandomNumberGenerator;

	r := randomGenerator 1;
	seed(r, 0);
	a := new(10, 0);
	default i:SingleInteger;
	for i in 1..10 repeat a.i := r();
	ok := true;
	seed(r, 0);
	for i in 1..10 repeat if a.i ~= r() then ok := false;
	ok;
}

print << "Testing random..." << newline;
sumitTest("random", random);
print << newline;
#endif

