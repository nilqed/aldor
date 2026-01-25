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
----------------------------- zpf.as ----------------------------------
#include "sumit"

macro {
	Z == SingleInteger;
	POLY == UnivariatePolynomialCategory0;
}

#if ASDOC
\thistype{ZechPrimeField}
\History{Manuel Bronstein}{24/5/95}{created}
\Usage{import from \this~p}
\Params{ {\em p} & SingleInteger & The characteristic\\ }
\Descr{\this~p implements the finite field $\ZZ_p$ using a cyclic
representation with discrete logarithm and exponential tables.
The prime $p$ must be odd.}
\begin{exports}
\category{PrimeFieldCategory}\\
\end{exports}
#endif

-- TEMPORARY: NEEDS with {} (BUGS 1035/1036)
-- ZechPrimeField(p:Z): SmallPrimeFieldCategory == {
ZechPrimeField(p:Z): SmallPrimeFieldCategory with {} == {
        -- sanity checks on the parameters
        ASSERT(p > 2);
	ASSERT(p < 2^(16@Z));
	ASSERT(odd? p);

	add {
	-- it turns out that it is more efficient to store the
	-- elements in the range [0,..,p-1] and use tables of
	-- logarithms and exponentials, than to store the exponents
	-- and use Zech logs for addition.
	macro Rep == Z;

	import from Rep;

	local gen:Z	== { import from PrimitiveRoots; primitiveRoot p; }
	local gtoi:Z := 1;
	local sp1:Z				== prev p;
	local disclog:PrimitiveArray Z		== new(sp1, 0);
	local discexp:PrimitiveArray Z		== new(sp1, 0);
	for i in 0..prev sp1 repeat {
		disclog.gtoi := i;		-- disclog[i] = log_g(i)
		discexp(next i) := gtoi;	-- discexp[i] = g^(i-1)
		gtoi := (gen * gtoi) rem p;	-- p is a half-word prime
	}

	0:%					== per 0;
	1:%					== per 1;
	karatsubaCutoff:	Z		== 40;
	fftCutoff:Z				== 1600;
	local p1:Integer			== sp1::Integer;
	zero?(a:%):Boolean			== zero? rep a;
	characteristic:Integer			== p::Integer;
	(a:%) = (b:%):Boolean			== rep a = rep b;
	lift(a:%):Z				== rep a;
	reduce(a:Z):%				== per(a rem p);
	(a:%) + (b:%):%				== per mmod_+(rep a, rep b, p);
	-(a:%):%			== { zero? a => a; per(p - rep a); }

	discreteLogTable():(PrimitiveArray Z, PrimitiveArray Z, Boolean) ==
		(disclog, discexp, true);

	(a:%) * (b:%):% == {
		zero? a or zero? b => 0;
		per discexp(next mmod_+(disclog rep a, disclog rep b, sp1));
	}

	(a:%) / (b:%):% == {
		ASSERT(~zero? b);
		zero? a => 0;
		per discexp(next mmod_-(disclog rep a, disclog rep b, sp1));
	}

	local mmod_+(a:Z, b:Z, q:Z):Z == {
		(c := a + b) < q => c;
		c - q;
	}

	local mmod_-(a:Z, b:Z, q:Z):Z == {
		(c := a - b) < 0 => c + q;
		c;
	}

	inv(a:%):% == {
		ASSERT(~zero? a);
		one? a => a;
		ASSERT(~zero?(disclog rep a));
		per discexp(p - disclog rep a);
	}

	(a:%)^(n:Integer):% == { 
		zero? a => 0;
		one? a => a;
		m:Z := retract(n mod p1);
		logan := (m * disclog rep a) rem sp1;	-- sp1 is  half-word
		n < 0 => {
			zero? logan => 1;
			per discexp(p - logan);
		}
		per discexp(next logan);
	}

	-- TEMPORARY: BAD 1.1.11e COMPILER BUG
	#:Integer			== characteristic$%;

	-- TEMPORARY: MUCH SLOWER IF INHERITED FROM CATring
	add!(a:%, b:%):%                == a + b;
	times!(a:%, b:%):%              == a * b;
	minus!(a:%):%                   == -a;
	}
}

#if SUMITTEST
---------------------- test zpf.as --------------------------
#include "sumittest"

macro F == ZechPrimeField 10007;

import from SingleInteger, F;

local inverse():Boolean == {
	a:F := 0;
	while zero? a repeat a := random();
	b := inv a;
	a * b = 1;
}

local exponentiate():Boolean == {
	import from Integer;
	a:F := 0;
	while zero? a repeat a := random();
	b := lift(random())::Integer;
	c:F := 1;
	for i in 1..b repeat c := c * a;
	a^b = c;
}

local sum():Boolean == {
	import from Integer;
	a:F := 0;
	while zero? a repeat a := random();
	b0:F := random();
	b := lift(b0)::Integer;
	c:F := 0;
	for i in 1..b repeat c := c + a;
	b0*a = c;
}

print << "Testing zpf..." << newline;
sumitTest("sum", sum);
sumitTest("inverse", inverse);
sumitTest("exponentiate", exponentiate);
print << newline;
#endif

