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
----------------------------- spf231.as ----------------------------------
#include "sumit"

#if ASDOC
\thistype{PrimeField231}
\History{Manuel Bronstein}{22/11/94}{created}
\Usage{import from \this}
\Descr{\this implements the finite field $\ZZ_{2^{31} - 1}$}
\begin{exports}
\category{SmallPrimeFieldCategory}\\
\end{exports}
#endif

-- TEMPORARY: NEEDS with {} (BUGS 1035/1036)
-- PrimeField231: PrimeFieldCategory == add {
PrimeField231: SmallPrimeFieldCategory with {} == add {
	macro {
		Z	== SingleInteger;
		p1	== 2147483646;
		charac	== 2147483647;
		Rep	== Z;
	}

	import from Rep;

	0:%					== per 0;
	1:%					== per 1;
	#:Integer				== charac;
	characteristic:Integer			== charac;
	sample:%				== 1;
	(a:%) + (b:%):%				== b32reduce(rep a + rep b);
	(a:%) = (b:%):Boolean			== rep a = rep b;
	lift(a:%):Z				== rep a;
	-(a:%):%				== per signfix(- rep a);
	(p:TextWriter) << (a:%):TextWriter	== p << rep a;
	integer(a:Literal):%			== per integer a;
	coerce(a:Integer):%			== per retract(a mod charac);
	coerce(a:Z):%				== reduce a;
	reduce(a:Z):%				== per(a mod charac);
	local signfix(a:Z):Z			== charac /\ (a + 1);
	local pfix(a:Z):%			== { a = charac => 0; per a }
	local b64?:Boolean		== wordSize$StandardUtilities = 64;
	local b32reduce(a:Z):%		== pfix(bit(a,31) => signfix a; a);
	(a:%) / (b:%):%	== { ASSERT(b ~= 0); mod_/(lift a, lift b, charac)::%; }
	inv(a:%):%	== { ASSERT(a ~= 0); mod_/(1, lift a, charac)::%; }

	(a:%) * (b:%):% == {
		b64? => b64product(a, b);
		-- This code assumes a 32-bit word size
		import from Machine;
		(hi, lo) := double_*((rep(a)::SInt) pretend Word,
					(rep(b)::SInt) pretend Word);
		h := shift((hi pretend SInt)::Z, 1);
		l := (lo pretend SInt)::Z;
		if bit(l, 31) then { h := h + 1; l := charac /\ l; }
		b32reduce(h + l);
	}

	-- This code assumes a 64-bit word size
	local b64product(a:%, b:%):% == {
		hilo := rep(a) * rep(b);
		l := hilo /\ charac;
		h := shift(hilo, -31);
		b32reduce(h + l);
	}

	-- TEMPORARY: TERRIBLE 1.1.11e COMPILER BUG
	extree(a:%):ExpressionTree        == extree lift a;
        pthPower(a:%):%                 == a;
	biglift(a:%):Integer		== lift(a)::Integer;

	-- TEMPORARY: MUCH SLOWER IF INHERITED FROM CATring
	add!(a:%, b:%):%                == a + b;
	times!(a:%, b:%):%              == a * b;
	minus!(a:%):%                   == -a;

	-- TEMPORARY: SEG FAULT IF FUNCTION IS NOT LOCAL (928)
	local times(a:%, b:%):% == a * b;
	(a:%)^(n:Integer):% == {
		import from BinaryPowering(%, times, Z);
		m:Z := retract(n mod p1);
		n < 0 => power(1, inv a, m);
		power(1, a, m);
	}
}

#if SUMITTEST
---------------------- test spf231.as --------------------------
#include "sumittest.as"

macro F == PrimeField231;

import from F;

inverse():Boolean == {
	a:F := 0;
	while zero? a repeat a := random();
	b := inv a;
	a * b = 1;
}

exponentiate():Boolean == {
	import from Integer;
	a:F := 0;
	while zero? a repeat a := random();
	b := lift(random())::Integer mod 10000;
	c:F := 1;
	for i in 1..b repeat c := c * a;
	a^b = c;
}

print << "Testing spf231..." << newline;
sumitTest("inverse", inverse);
sumitTest("exponentiate", exponentiate);
print << newline;
#endif

