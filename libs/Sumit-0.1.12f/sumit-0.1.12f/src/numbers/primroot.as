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
----------------------------- primroot.as ----------------------------------
#include "sumit.as"

#if ASDOC
\thistype{PrimitiveRoots}
\History{Manuel Bronstein}{8/6/95}{created}
\Usage{import from \this}
\Descr{\this~implements functionalities needed to compute generators
of small cyclic groups.}
\begin{exports}
divisors & Z $\to$ List Z & List of divisors\\
primitiveRoot & Z $\to$ Z & Modular primitive root\\
\end{exports}
\Aswhere{
Z & == & SingleInteger\\
}
#endif

macro {
	ARR	== Array;
	Z	== SingleInteger;
	NPRIMES	== 1000;
}

PrimitiveRoots: with {
	divisors: Z -> List Z;
#if ASDOC
\aspage{divisors}
\Usage{\name~n}
\Signature{SingleInteger}{List SingleInteger}
\Params{ {\em n} & SingleInteger & An integer\\ }
\Retval{Returns all the divisors $d$ of $n$ with $1 < d < \abs n$.}
#endif
	primitiveRoot: Z -> Z;
#if ASDOC
\aspage{primitiveRoot}
\Usage{\name~p}
\Signature{SingleInteger}{SingleInteger}
\Params{ {\em p} & SingleInteger & A prime\\ }
\Retval{Returns a generator of the multiplicative group
$(\ZZ/p \ZZ)^\ast$.}
\Remarks{The argument $p$ must be a prime number, otherwise this function
returns any integer with no significance.}
#endif
} == add {
	import from Z, ARR Z;

	-- primitive roots for the first NPRIMES odd primes
	primroots:ARR(Z) := [2,2,3,2,2,3,2,5,2,3,2,6,3,5,2,2,2,2,7,5,3,2,3,5,_
		2,5,2,6,3,3,2,3,2,2,6,5,2,5,2,2,2,19,5,2,3,2,3,2,6,3,7,7,6,3,_
		5,2,6,5,3,3,2,5,17,10,2,3,10,2,2,3,7,6,2,2,5,2,5,3,21,2,2,7,5,_
		15,2,3,13,2,3,2,13,3,2,7,5,2,3,2,2,2,2,2,3,3,5,2,3,7,7,3,2,3,_
		2,3,3,11,5,2,2,2,5,2,5,3,2,2,11,5,6,3,5,3,2,6,11,2,2,2,3,3,2,_
		3,2,2,11,2,3,2,5,2,3,2,5,2,17,7,3,5,2,2,3,5,6,3,5,6,7,11,3,2,_
		10,14,5,3,3,7,2,3,6,3,2,5,3,5,2,2,2,11,17,5,5,2,7,2,3,11,2,3,_
		5,2,3,2,7,2,2,3,2,6,2,10,2,6,2,13,13,3,3,5,2,2,13,3,3,2,6,3,7,_
		3,2,2,3,6,3,2,5,14,2,2,11,2,2,5,2,3,19,3,2,3,5,11,3,5,7,3,2,2,_
		3,2,11,3,2,2,2,3,3,3,3,3,2,2,2,7,6,5,10,2,6,11,6,5,3,5,2,2,14,_
		10,2,6,3,2,2,3,2,5,2,3,2,2,2,5,2,3,5,3,5,2,2,7,2,5,2,3,2,5,7,_
		2,7,5,3,2,10,2,3,3,23,7,5,5,2,2,2,3,2,7,2,2,3,7,19,2,5,2,3,2,_
		2,7,3,13,2,2,5,3,5,2,3,11,6,3,5,2,6,5,2,2,5,2,3,17,2,2,5,2,6,_
		2,2,7,7,3,5,2,3,3,3,2,5,7,2,2,5,19,2,2,2,7,5,3,3,3,2,6,3,3,3,_
		2,6,2,3,2,2,5,2,2,2,11,2,7,5,3,5,2,5,5,2,13,2,2,3,10,17,14,2,_
		2,5,2,3,11,6,2,6,2,3,6,7,7,3,3,5,7,7,2,11,2,3,5,10,6,6,2,3,3,_
		3,2,6,2,10,6,2,3,3,5,2,11,22,2,5,3,3,5,2,5,3,7,2,3,2,2,2,2,7,_
		2,5,17,2,2,7,2,2,3,2,2,3,3,5,2,3,5,15,2,2,2,13,5,2,2,5,2,2,7,_
		3,2,7,3,5,7,2,5,2,2,3,3,3,5,2,2,5,2,13,11,2,13,2,3,2,3,2,3,2,_
		6,2,3,2,5,2,2,2,3,3,10,5,3,11,2,2,2,12,5,13,2,2,5,2,3,5,11,6,_
		3,2,2,3,3,2,2,2,2,7,5,2,3,5,3,3,10,2,2,2,2,14,2,3,3,3,21,3,2,_
		3,5,3,2,2,2,7,2,3,5,2,6,11,3,5,11,5,2,2,2,3,5,3,3,15,3,3,11,2,_
		5,6,2,17,5,19,3,6,2,2,3,7,7,2,3,3,11,11,2,3,3,6,13,6,2,3,7,6,_
		2,5,11,2,2,5,3,2,3,2,3,3,11,2,2,2,3,5,2,6,2,19,3,2,5,6,2,2,2,_
		7,17,2,7,10,3,2,3,7,7,3,5,2,5,2,3,11,3,2,3,7,3,5,3,3,3,5,3,2,_
		7,7,2,3,2,2,3,2,13,11,5,10,2,2,13,2,6,11,5,7,14,3,2,5,3,2,3,2,_
		11,2,2,19,2,5,2,10,2,2,7,6,3,5,2,6,2,6,2,3,2,7,3,5,2,11,31,3,_
		5,2,5,2,7,3,2,3,2,2,5,5,5,2,2,10,17,3,7,2,3,7,2,5,5,3,3,2,2,3,_
		2,2,5,3,2,5,3,5,2,11,2,7,2,10,7,2,2,3,10,3,3,13,19,3,2,2,2,2,_
		6,3,3,3,2,3,7,2,6,7,2,17,10,5,3,3,5,14,13,3,2,2,2,2,6,5,7,3,2,_
		2,5,2,11,2,3,3,2,2,2,7,10,2,3,2,2,3,22,3,5,2,3,2,2,2,7,2,2,2,_
		7,13,5,2,3,5,6,5,3,2,2,2,3,2,5,2,7,5,2,3,5,7,7,3,10,2,3,3,2,5,_
		2,2,2,2,5,2,2,5,2,6,7,2,6,2,6,7,5,2,5,3,2,3,2,2,6,5,7,2,2,2,2,_
		3,7,2,2,2,13,13,2,3,5,2,6,2,5,2,7,2,3,2,3,17,6,2,3,5,2,3,5,7,_
		10,2,3,2,3,3,5,2,12,2,3,5,2,3,2,2,2,7,3];

	divisors(n:Z):List Z == {
		ASSERT(n >= 0);
		import from SmallPrimes;
		n < 2 or primeIndex(n) ~= 0 => empty();
		even? n => cons(2, divisors1 deflate(n, 2));
		divisors1 n;
	}

	divisors1(n:Z):List Z == {
		ASSERT(odd? n);
		import from Integer, List Z;
		import from DoubleFloat, DoubleFloatElementaryFunctions;
		i:Z := 3;
		l:List Z := empty();
		bound:Z := retract round sqrt(n::DoubleFloat);
		while i < bound repeat {
			zero?(n rem i) => {
				l := cons(i, l);
				n := deflate(n, i);
				bound := retract round sqrt(n::DoubleFloat);
			}
			i := i + 2;
		}
		l;
	}

	deflate(n:Z, m:Z):Z == {
		r:Z := 0;
		while zero? r repeat {
			(q, r) := divide(n, m);
			if zero? r then n := q;
		}
		n;
	}

	primRoot?(n:Z, p:Z, l:List Z):Boolean == {
		for e in l repeat { mod_^(n, e, p) = 1 => return false; }
		true;
	}

	primitiveRoot(p:Z):Z == {
		import from List Z, SmallPrimes;
		ASSERT(p > 1);
		p = 2 => 1;
		(i := primeIndex p) ~= 0 and i <= NPRIMES => primroots.i;
		l:List Z := [p1 quo d for d in divisors(p1 := p - 1)];
		for j in 2..p1 repeat { primRoot?(j, p, l) => return j; }
		0;
	}
}
