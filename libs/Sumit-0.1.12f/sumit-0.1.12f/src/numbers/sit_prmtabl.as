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
---------------------------- sit_prmtabl.as ---------------------------------
--
-- Interface to hard-coded tables of primes
--
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"

macro Z	== MachineInteger;

define PrimeTable: Category == with {
	primes: Array Z;	-- the actual primes
	fourier: Array Z;	-- fourier primes
	roots: Array Z;		-- either primitive roots for primes
				-- or primitive roots of 1 for fourier primes
};

#if ALDOC
\thistype{PrimeCollection}
\History{Manuel Bronstein}{26/4/96}{created}
\Usage{\this: Category}
\Descr{\this~is the category of collections of primes with various
properties and various sizes.}
\begin{exports}
\asexp{allPrimes}: & () $\to$ \astype{Generator} Z & Generate all the primes\\
\asexp{fourierPrime}: & Z $\to$ (Z, Z) & Fourier prime\\
\asexp{maxPrime}: & $\to$ Z & Largest prime\\
\asexp{nextPrime:} & Z $\to$ Z & First prime above a given number\\
\asexp{previousPrime:} & Z $\to$ Z & First prime below a given number\\
\asexp{primRoot:} & Z $\to$ Z & Modular primitive root\\
\asexp{randomPrime:} & () $\to$ Z & Random prime\\
\end{exports}
\begin{aswhere}
Z & == & \astype{MachineInteger}\\
\end{aswhere}
#endif

define PrimeCollection: Category == with {
	allPrimes: () -> Generator Z;
#if ALDOC
\aspage{allPrimes}
\Usage{ for p in \name() repeat \{ \dots \} }
\Signature{()}{\astype{Generator} \astype{MachineInteger}}
\Descr{This function allows a loop to iterate over all the primes
provided by the collection.}
#endif
	fourierPrime: Z -> (Z, Z);
#if ALDOC
\aspage{fourierPrime}
\Usage{\name~n}
\Signature{\astype{MachineInteger}}
{(\astype{MachineInteger},\astype{MachineInteger})}
\Retval{Returns $(p,\omega)$ such that $p$ is a prime of the form
$p = 2^n k + 1$ with $k$ odd, and $\omega$ is a primitive $\sth{2^n}$
root of unity in $\mathbbm{F}_p$. Returns $(0,0)$ if $n$ is too large.}
#endif
	maxPrime: Z;
#if ALDOC
\aspage{maxPrime}
\Usage{\name}
\Signature{}{\astype{MachineInteger}}
\Retval{Returns the largest prime in the collection.}
#endif
	nextPrime: Z -> Z;
#if ALDOC
\aspage{nextPrime}
\Usage{\name~n}
\Signature{\astype{MachineInteger}}{\astype{MachineInteger}}
\Params{ {\em n} & \astype{MachineInteger} & An integer\\ }
\Retval{Returns the smallest prime $p$ in the collection with $n < p$,
$0$ if there are none.}
\seealso{previousPrime(\this), randomPrime(\this)}
#endif
	previousPrime: Z -> Z;
#if ALDOC
\aspage{previousPrime}
\Usage{\name~n}
\Signature{\astype{MachineInteger}}{\astype{MachineInteger}}
\Params{ {\em n} & \astype{MachineInteger} & An integer\\ }
\Retval{Returns the largest prime $p$ in the collection with $n > p$,
$0$ if there are none.}
\seealso{nextPrime(\this), randomPrime(\this)}
#endif
	primRoot: Z -> Z;
#if ALDOC
\aspage{primRoot}
\Usage{\name~p}
\Signature{\astype{MachineInteger}}{\astype{MachineInteger}}
\Params{ {\em p} & \astype{MachineInteger} & A prime\\ }
\Retval{Returns a generator of the multiplicative group
$(\ZZ/p \ZZ)^\ast$ or $0$ if $p$ is not a prime in the table,
or is no primitive root is stored.}
\seealso{primitiveRoot(\astype{PrimitiveRoots})}
#endif
	randomPrime: () -> Z;
#if ALDOC
\aspage{randomPrime}
\Usage{\name()}
\Signature{()}{\astype{MachineInteger}}
\Retval{Returns a random prime in the collection.}
\seealso{nextPrime(\this), previousPrime(\this)}
#endif
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
		index >= nprimes => maxPrime;
		oddPrime index;
	}

	-- check bounds and returns 0 if out of bounds
	local oddPrime(index:Z):Z == {
		TRACE("oddPrime: ", index);
		index < 0 or index >= nprimes => 0;
		primes.index;
	}

	-- return (found?, i) such that:
	--   if found? is true, then n = wordprimes.i
	--   if found? is false, then:
	--	if 0 <= i < nprimes-1, then wordprimes.i < n < wordprimes(i+1)
	--	if i = nprimes-1 then wordprimes(nprimes - 1) < n
	local search(n:Z):(Boolean, Z) == {
		import from Array Z;
		binarySearch(primes, n);
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

