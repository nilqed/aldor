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
----------------------------- fixedprimes.as ----------------------------------
#include "sumit"

macro Z == SingleInteger;

FixedPrimes(T:PrimeTable): PrimeCollection == add {
	local primes:Array Z	== primes$T;
	local fourier:Array Z	== fourier$T;
	local roots:Array Z	== roots$T;
	local nprimes:Z		== #primes;
	local nfourier:Z	== #fourier;
	maxPrime:Z		== primes.nprimes;

	fourierPrime(n:Z):(Z, Z) == {
		n < 1 or n > nfourier => (0, 0);
		(fourier.n, roots.n);
	}

	nextPrime(n:Z):Z == {
		(found?, index) := search n;
		oddPrime next index;
	}

	previousPrime(n:Z):Z == {
		(found?, index) := search n;
		found? => oddPrime prev index;
		oddPrime index;
	}

	local oddPrime(index:Z):Z == {
		TRACE("oddPrime: ", index);
		index < 1 or index > nprimes => 0;
		primes.index;
	}

	randomPrime():Z == {
		import from Integer;
		n := random()$Integer mod (nprimes::Integer);
		primes(next retract n);
	}

	-- return i such that wordprimes.i <= n < wordprimes(i+1)
	local search(n:Z):(Boolean, Z) == {
		import from BinarySearch(Z, Z);
		binarySearch(n, (m:Z):Z +-> primes.m, 1, nprimes);
	}
}
