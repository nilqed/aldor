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
------------------------------ modpge.as ------------------------------------
#include "sumit"

#if ASDOC
\thistype{ModulopGaussElimination}
\History{Thom Mulders}{8 July 96}{created OGE for general fields}
\History{Manuel Bronstein}{15 December 98}{adapted for machine primes}
\Usage{import from \this}
\begin{exports}
\category{EliminationCategory(R,M)}\\
\end{exports}
\Descr{
This domain implements ordinary Gaussian elimination on matrices
modulo a machine prime.
}
#endif

macro {
	Z == SingleInteger;
	A == PrimitiveArray Z;
	M == PrimitiveArray A;
	-- GAMMA is an upper bound on the ratio (remainder/compare)
	-- for machine integers (actual value depend on hardware)
	GAMMA == 50;
}

ModulopGaussElimination: with {
	dependence: (Generator A, Z, Z) -> (M, A, Z, Z);
	deter: (M, Z, Z, A, Z, A, Z, Z) -> Z;
	determinant!: (M, Z, Z, Z) -> Z;
	extendedRowEchelon!: (M, Z, Z, Z) -> (A, Z, A, Z, M);
	rowEchelon!: (M, Z, Z, Z) -> (A, Z, A, Z);
} == add {
	local maxhalf:Z == maxPrime$HalfWordSizePrimes;
	local maxint:Z	== max$Z;

#if ASTRACE
	local prt(str:String, a:A, n:Z):() == {
		print << str;
		for i in 1..n repeat print << a.i << " ";
		print << newline;
	}

	local prt(str:String, a:M, r:Z, c:Z):() == {
		print << str << " = ";
		for i in 1..r repeat prt("", a.i, c);
		print << newline;
	}
#else
	local prt(str:String, a:A, n:Z):()	== {};
	local prt(str:String, a:M, r:Z, c:Z):() == {};
#endif

	rowEchelon!(a:M, ra:Z, ca:Z, p:Z):(A, Z, A, Z) == {
		prt("modpge::rowEchelon!: a", a, ra, ca);
		TRACE("modpge::rowEchelon!: p = ", p);
		rowEch!(a, ra, ca, new 0, ra, 0, p);
	}

	extendedRowEchelon!(a:M, ra:Z, ca:Z, p:Z):(A, Z, A, Z, M) == {
		b:M := new ra;
		for i in 1..ra repeat {
			b.i := new(ra, 0);
			b.i.i := 1;
		}
		(pp, r, st, d) := rowEch!(a, ra, ca, b, ra, ra, p);
		(pp, r, st, d, b);
	}

	dependence(gen:Generator A, n:Z, p:Z):(M, A, Z, Z) == {
		assert(n > 0); assert(p > 1);
		p > maxhalf => fullDep(gen, n, p);
		halfDep(gen, n, p);
	}

	determinant!(a:M, ra:Z, ca:Z, p:Z):Z == {
		(pp, r, st, d) := rowEchelon!(a, ra, ca, p);
		deter(a, ra, ca, pp, r, st, d, p);
	}

	deter(a:M, ra:Z, ca:Z, pp:A, r:Z, st:A, d:Z, p:Z):Z == {
		prt("modpge::deter:a", a, ra, ca);
		prt("modpge::deter:pp = ", pp, ra);
		TRACE("modpge::deter:r = ", r);
		prt("modpge::deter:st = ", st, ca);
		TRACE("modpge::deter:d = ", d);
		TRACE("modpge::deter: p = ", p);
		assert(ra = ca); assert(p > 1);
		p > maxhalf => fullDeter(a, ra, ca, pp, r, st, d, p);
		halfDeter(a, ra, ca, pp, r, st, d, p);
	}

	local rowEch!(a:M, ra:Z, ca:Z, b:M, rb:Z, cb:Z, p:Z):(A, Z, A, Z) == {
		prt("modpge::rowEch!: a", a, ra, ca);
		prt("modpge::rowEch!: b", b, rb, cb);
		TRACE("modpge::rowEch!: p = ", p);
		assert(ra = rb); assert(p > 1);
		p > maxhalf => fullRowEch!(a, ra, ca, b, rb, cb, p);
		-- from normalized inputs, the first k loops cannot overflow
		k := prev(maxint quo (prev(p)^2));
		k > GAMMA or 4*k > ra => halfRowEch!(a, ra, ca, b, rb, cb, k,p);
		halfRowEch!(a, ra, ca, b, rb, cb, p);
	}

-- Those 2 files contain similar code with 2 different product functions
-- (the product is not passed as parameter because the function-call
--  overhead is too high, and this would prevent inlining)
#include "fullge.as"
#include "halfge.as"
}

