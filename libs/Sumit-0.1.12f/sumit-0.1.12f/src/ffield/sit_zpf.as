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
--------------------------- sit_zpf.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"

macro {
	Z == MachineInteger;
	A == PrimitiveArray;
}

#if ALDOC
\thistype{ZechPrimeField}
\History{Manuel Bronstein}{24/5/95}{created}
\Usage{import from \this~p}
\Params{ {\em p} & SingleInteger & The characteristic\\ }
\Params{ {\em p} & \astype{MachineInteger} & The characteristic\\ }
\Descr{\this~p implements the finite field $\ZZ / p \ZZ$, using
discrete logarithm and exponential tables for multiplication, where $p\in \ZZ$
is a word--size prime.}
\begin{exports}
\category{\astype{SmallPrimeFieldCategory}}\\
\end{exports}
#endif

ZechPrimeField(p:Z): SmallPrimeFieldCategory == {
        -- sanity checks on the parameters
        assert(p > 2);
	assert(p < shift(1, 16));	-- 2^16 w/o importing from Integer
	assert(odd? p);

	add {
	-- it turns out that it is more efficient to store the
	-- elements in the range [0,..,p-1] and use tables of
	-- logarithms and exponentials, than to store the exponents
	-- and use Zech logs for addition.
	Rep == Z;

	import from Rep;

	local gen:Z	== { import from PrimitiveRoots; primitiveRoot p; }
	local gtoi:Z := 1;
	local sp1:Z				== prev p;
	local disclog:A Z			== new(p, 0);
	local discexp:A Z			== new(p, 0);
	for i in 0..prev sp1 repeat {
		disclog.gtoi := i;		-- disclog[i] = log_g(i)
		discexp.i := gtoi;		-- discexp[i] = g^i
		gtoi := (gen * gtoi) rem p;	-- p is a half-word prime
	}
	assert(gtoi = 1);
	discexp.sp1 := 1;

	0:%					== per 0;
	1:%					== per 1;
	karatsubaCutoff:	Z		== 40;
	-- fftCutoff:Z				== 1600;
	local pp:Integer			== p::Integer;
	local p1:Integer			== sp1::Integer;
	characteristic:Integer			== p::Integer;
	(a:%) = (b:%):Boolean			== rep a = rep b;
	lift(a:%):Integer			== rep(a)::Integer;
	coerce(a:Integer):%			== per machine(a mod pp);
	(a:%) + (b:%):%				== per mmod_+(rep a, rep b, p);
	-(a:%):%			== { zero? a => a; per(p - rep a); }

	discreteLogTable:Cross(A Z, A Z, Boolean) == {
		import from Boolean;
		(disclog, discexp, true);
	}

	(a:%) * (b:%):% == {
		zero? a or zero? b => 0;
		per discexp(mmod_+(disclog rep a, disclog rep b, sp1));
	}

	(a:%) / (b:%):% == {
		import from Boolean;
		assert(~zero? b);
		zero? a => 0;
		per discexp(mod_-(disclog rep a, disclog rep b, sp1));
	}

	-- slightly faster than mmod_+ since we know that a+b cannot overflow
	local mmod_+(a:Z, b:Z, q:Z):Z == {
		(c := a + b) < q => c;
		c - q;
	}

	inv(a:%):% == {
		import from Boolean;
		assert(~zero? a);
		per discexp(sp1 - disclog rep a);
	}

	(a:%)^(n:Integer):% == { 
		zero? a => 0;
		one? a or zero?(m := machine(n mod p1)) => 1;
		logan := (m * disclog rep a) rem sp1;	-- sp1 is  half-word
		per discexp logan;
	}

	-- TEMPORARY: BUG 1181
	#:Integer		== characteristic$%;

	-- THOSE ARE BETTER THAN THE CORRESPONDING CATEGORY DEFAULTS
	zero?(a:%):Boolean	== zero? rep a;
	one?(a:%):Boolean	== one? rep a;
	add!(a:%, b:%):%	== a + b;
	times!(a:%, b:%):%	== a * b;
	coerce(a:Z):%		== per(a mod p);
	machine(a:%):Z		== rep a;
	(a:%) - (b:%):%	== { (c := rep a - rep b) < 0 => per(c + p); per c }

	-- TEMPORARY (BUG1182) DEFAULTS DON'T INLINE WELL
	minus!(a:%):%		== -a;
	}
}

#if SUMITTEST
---------------------- test zpf.as --------------------------
#include "sumittest"

macro F == ZechPrimeField 10007;

import from MachineInteger, F;

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
	b := lift random();
	c:F := 1;
	for i in 1..b repeat c := c * a;
	a^b = c;
}

local sum():Boolean == {
	import from Integer;
	a:F := 0;
	while zero? a repeat a := random();
	b0:F := random();
	b := lift b0;
	c:F := 0;
	for i in 1..b repeat c := c + a;
	b0 * a = c;
}

stdout << "Testing sit__zpf..." << endnl;
sumitTest("sum", sum);
sumitTest("inverse", inverse);
sumitTest("exponentiate", exponentiate);
stdout << endnl;
#endif

