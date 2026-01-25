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
--------------------------------- modla.as --------------------------------
--
-- Copyright (c) Institute of Scientific Computation, ETH Zurich, 1995
--

#include "sumit"

#if ASDOC
\thistype{ModularLinearAlgebra}
\History{Manuel Bronstein}{15/12/98}{created}
\Usage{import from \this(Z, M)}
\Params{
{\em Z} & IntegerCategory & An integer-like ring\\
{\em M} & MatrixCategory0 Z & Matrices over Z\\
}
\Descr{\this~provides modular algorithms for
matrices over the integers, using Hensel lifting and
the Chinese Remainder Theorem.}
\begin{exports}
crtDeterminant: & M $\to$ Partial Z & CRT determinant\\
hadamard: & M $\to$ Z & Hadamard bound\\
modularDeterminant: & (M, Z) $\to$ Partial Z & modular determinant\\
\end{exports}
#endif

macro {
	I == SingleInteger;
	A == PrimitiveArray;
}

ModularLinearAlgebra(Z:IntegerCategory, M:MatrixCategory0 Z): with {
	crtDeterminant: M -> Partial Z;
#if ASDOC
\aspage{crtDeterminant}
\Usage{\name~m}
\Signature{M}{Partial Z}
\Params{ {\em m} & M & a matrix over Z\\ }
\Retval{Returns the determinant of m or \failed.}
\Remarks{This algorithm can fail because it runs out of primes. This will happen
if the determinant has than around 3000 digits.}
#endif
	hadamard: M -> Z;
#if ASDOC
\aspage{hadamard}
\Usage{\name~m}
\Signature{M}{Z}
\Params{ {\em m} & M & a matrix over Z\\ }
\Retval{Returns the Hadamard bound on the determinant of m, \ie an integer
$h$ such that $| \mbox{det}(m) | \le h$.}
#endif
	modularDeterminant: M -> Partial Z;
	modularDeterminant: (M, Z, I, I) -> Partial Z;
	inverseAndDeterminant: M -> (M, I, I);
} == add {
	modularDeterminant(m:M):Partial Z == {
		import from I;
		-- TEMPORARY: SHOULD MAKE ROWS AND COLUMNS PRIMITIVE
		START__TIME;
		(m1, dp, p) := inverseAndDeterminant m;
		TIME("modla::modularDeterminant: inverse mod p at ");
		zero? dp => failed;	-- TEMPORARY
		moddet(m, m1, dp, p);
	}

	local moddet(m:M, m1:M, dp:I, p:I):Partial Z == {
		macro {
			F == SmallPrimeField p;
			Mp == DenseMatrix F;
		}
		START__TIME;
		import from Integer, Z, F, Mp, HenselSolve(Z, M, F, Mp);
		n := rows m;
		assert(n = cols m);
		pz := p::Integer;
		mp:Mp := zero(n, n);
		for i in 1..n repeat for j in 1..n repeat
			mp(i, j) := reduce retract(integer(m1(i, j)) mod pz);
		rhs:M := random(n, 2);
		TIME("modla::modularDeterminant: matrix reduced mod p at ");
		(sol1, den1) := henselSolve(m, mp, column(rhs, 1));
		TIME("modla::modularDeterminant: first hensel at ");
		-- (sol2, den2) := henselSolve(m, mp, column(rhs, 2));
		TIME("modla::modularDeterminant: second hensel at ");
		-- d := lcm(den1, den2);
		d := den1;
		TIME("modla::modularDeterminant: lcm at ");
		u := modularDeterminant(m, d, p, dp);
		TIME("modla::modularDeterminant: determinant at ");
		u;
	}

	-- returns (m^(-1) mod p, det(m) mod p, p)
	inverseAndDeterminant(m:M):(M, I, I) == {
		import from Z, Integer, A I, A A I, ModulopGaussElimination;
		n := rows m;
		assert(n = cols m);
		p := getPrime(-1, 1);
		pz := p::Integer;
		assert(~zero? p);
		mp:A A I := new n;
		for i in 1..n repeat {
			mp.i := new n;
			for j in 1..n repeat
				mp.i.j := retract(integer(m(i, j)) mod pz);
		}
		(pp, r, st, d, w) := extendedRowEchelon!(mp, n, n, p);
		det := deter(mp, n, n, pp, r, st, d, p);	-- det mod p
		(backsolve(mp, n, pp, st, r, w, p), det, p);
	}

	local backsolve(m:A A I, n:I, pp:A I, st:A I, r:I, w:A A I, p:I):M == {
		macro {
			F == SmallPrimeField p;
			Mp == DenseMatrix F;
		}
		import from F, Z, Mp, Backsolve(F, Mp);
		mm:Mp := zero(n, n);
		ww:Mp := zero(n, n);
		for i in 1..n repeat for j in 1..n repeat {
			mm(i,j) := reduce(m.i.j);
			ww(i,j) := reduce(w.i.j);
		}
		-- den must be a primitive array of 1's
		(sol, den) := backsolve(mm, pp, st, r, ww);
		m1:M := zero(n, n);
		for i in 1..n repeat for j in 1..n repeat
			m1(i,j) := lift(sol(i,j))::Z;
		m1;
	}

	crtDeterminant(m:M):Partial Z == {
		import from I, A I, A A I, Z;
		p := getPrime(-1, 1);
		assert(~zero? p);
		-- TEMPORARY: SHOULD MAKE ROWS AND COLUMNS PRIMITIVE
		-- create a buffer for m mod p
		n := rows m;
		assert(n = cols m);
		mp:A A I := new n;
		for i in 1..n repeat mp.i := new n;
		TRACE("moddet::crtDeterminant:trying prime ", p::Z);
		det := tryprime(m, n, mp, 1, p);	-- balanced rep
		moddet(m, 1, hadamard m, mp, p, det);
	}

	-- m = matrix over Z
	-- d = known factor of det(m)
	-- p = machine prime
	-- dp = det(m) mod p
	modularDeterminant(m:M, d:Z, p:I, dp:I):Partial Z == {
		import from Integer, A I, A A I;
		TRACE("moddet::modularDeterminant:m = ", m);
		TRACE("moddet::modularDeterminant:d = ", d);
		TRACE("moddet::modularDeterminant:p = ", p);
		TRACE("moddet::modularDeterminant:dp = ", dp);
		-- create a buffer for m mod p
		n := rows m;
		assert(n = cols m);
		mp:A A I := new n;
		for i in 1..n repeat mp.i := new n;
		pz := p::Integer;
		if d ~= 1 then {		-- must compute (dp/d) mod p
			if dp < 0 then dp := dp + p;	-- unsigned rep
			dp := mod_/(dp, retract(integer(d) mod pz), p);
		}
		pover2 := shift(p, -1);			-- floor(p/2) = (p-1)/2
		if dp > pover2 then dp := dp - p;	-- balanced rep
		moddet(m, d, next(hadamard(m) quo abs(d)), mp, p, dp);
	}

	hadamard(m:M):Z == {
		import from I, Integer;
		n := rows m;
		assert(n > 0); assert(n = cols m);
		rnorm:Z := 1; cnorm:Z := 1;
		for i in 1..n repeat {
			rnorm := rnorm * rowNorm(m, i, n);
			cnorm := cnorm * colNorm(m, i, n);
		}
		mu := min(rnorm, cnorm);
		(square?, root) := nthRoot(mu, 2);
		square? => root;
		next root;
	}

	-- 2-norm of col i
	local colNorm(m:M, i:I, n:I):Z == {
		import from Integer;
		nrm:Z := 0;
		for j in 1..n repeat nrm := nrm + m(j, i)^2;
		nrm;
	}

	-- 2-norm of row i
	local rowNorm(m:M, i:I, n:I):Z == {
		import from Integer;
		nrm:Z := 0;
		for j in 1..n repeat nrm := nrm + m(i, j)^2;
		nrm;
	}

	-- returns a new prime less than p, goes in descending order
	local getPrime(p:I, n:Z):I == {
		-- Use lazy half-word primes to allow lazy determinants mod p
		import from LazyHalfWordSizePrimes, Partial Z;
		p := { p < 0 => maxPrime; previousPrime p; }
		while (~zero? p) and ~failed?(exactQuotient(n, p::Z)) repeat
			p := previousPrime p;
		p;
	}

	-- returns det(m)/den
	-- p = machine prime
	-- det = (det(m)/den) mod p (balanced rep)
	local moddet(m:M, den:Z, bound:Z, mp:A A I, p:I, dp:I):Partial Z == {
		import from A I, Integer, ChineseRemaindering Z;
		TRACE("moddet::moddet:den = ", den);
		TRACE("moddet::moddet:bound = ", bound);
		TRACE("moddet::moddet:p = ", p);
		TRACE("moddet::moddet:dp = ", dp);
		n := rows m;
		assert(n = cols m);
		modulus := p::Z;
		det := dp::Z;
		signedBound := next(bound + bound);	-- allow for +/-
		while modulus < signedBound repeat {
			zero?(p := getPrime(p, den)) => return failed;
			TRACE("moddet::moddet:trying prime ", p::Z);
			d := tryprime(m, n, mp, den, p);	-- det/den
			det := combine(modulus, p)(det, d);
			modulus := (p::Z) * modulus;
		}
		[den * det];
	}

	-- returns the determinant of m modulo p in balanced representation
	local tryprime(m:M, n:I,  mp:A A I, den:Z, p:I):I == {
		import from Integer, ModulopGaussElimination;
		pz := p::Integer;
		pover2 := shift(p, -1);		-- floor(p/2) = (p-1)/2
		for i in 1..n repeat for j in 1..n repeat
			mp.i.j := retract(integer(m(i, j)) mod pz);
		d := determinant!(mp, n, n, p);
		if den ~= 1 then d := mod_/(d, retract(integer(den) mod pz), p);
		d > pover2 => d - p;
		d;
	}
}
