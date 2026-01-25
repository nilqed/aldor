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
----------------------------- mpf.as ----------------------------------
#include "sumit"

#if ASDOC
\thistype{MontgomeryPrimeField}
\History{Manuel Bronstein}{14/11/95}{created}
\Usage{import from \this~p}
\Params{ {\em p} & Integer & The characteristic\\ }
\Descr{\this~p implements the finite field $\ZZ_p$ using
the arithmetic described in:
P.~Montgomery, {\em Modular Multiplication without Trial Division\/},
Mathematics of Computation {\bf 44}, 519--521 (1985).
This type should be faster than {\tt BigPrimeField} for large $p$.}
\begin{exports}
\category{PrimeFieldCategory}\\
\end{exports}
#endif

macro Z == Integer;

-- TEMPORARY: NEEDS with {} (BUGS 1035/1036)
-- MontgomeryPrimeField(p:Z): PrimeFieldCategory == {
MontgomeryPrimeField(p:Z): PrimeFieldCategory with {} == {
        -- sanity checks on the parameters
        ASSERT(p > 2);

	add {
	macro Rep == IntegerMod p;

	import from Rep;

	local p1:Z			== prev p;
 	local logp:SingleInteger	== length p;
	local mlogp:SingleInteger	== - logp;
	local R:Z			== shift(1@Z, logp);
	0:%				== per 0;
	1:%				== per(R::Rep);
	local maskremR:Z		== shift(R, 1) - 1;
	#:Z				== p;
	local mulR(n:Z):Z		== shift(n, logp);
	local quoR(n:Z):Z		== shift(n, mlogp);
	(a:%) = (b:%):Boolean		== rep a = rep b;
	(a:%) + (b:%):%			== per(rep a + rep b);
	-(a:%):%			== per(- rep a);

	-- TEMPORARY: NEED A BITWISE and ON BIGINT!!!
	-- remR(n:Z):Z			== n /\ maskremR;
	local remR(n:Z):Z		== n - shift(quoR n, logp);

	inv(a:%):%			== 1 / a;
	integer(s:Literal):%		== (integer(s)@Z)::%;
	coerce(n:Z):%			== per(mulR(n)::Rep);
	coerce(n:SingleInteger):%	== reduce n;
	reduce(a:SingleInteger):%	== a::Z::%;
	biglift(a:%):Z			== f(lift rep a);
	lift(a:%):SingleInteger		== retract biglift a;
	characteristic:Z		== p;
	local Z2MPF(n:Z):%		== per(n::Rep);
	(a:%) * (b:%):%			== Z2MPF f(lift(rep a) * lift(rep b));
	-- v = - p^{-1} mod R
	local v:Z == { import from Partial Z; retract diophantine(p, -1, R) };

	local f(z:Z):Z == {	-- computes z R^{-1} mod p without division
		m := remR(v * remR z);
		t := quoR(z + m * p);
		t >= p => t - p;
		t;
	}

	(a:%) / (b:%):% == {
		import from Partial Z;
		Z2MPF retract diophantine(f lift rep b, lift rep a, p);
	}

	-- TEMPORARY: SEG FAULT IF FUNCTION IS NOT LOCAL (928)
	times(a:%, b:%):% == a * b;
	(a:%)^(n:Z):% == {
		import from BinaryPowering(%, times, Z);
		m := n mod p1;
		n < 0 => power(1, inv a, m);
		power(1, a, m);
	}
	}
}

#if SUMITTEST
---------------------- test mpf.as --------------------------
#include "sumittest.as"

macro F == MontgomeryPrimeField 57952155664616982751;

import from Integer, F;

inverse():Boolean == {
	a:F := 0;
	while zero? a repeat a := random();
	b := inv a;
	a * b = 1;
}

exponentiate():Boolean == {
	import from SingleInteger, Integer;
	a:F := 0;
	while zero? a repeat a := random();
	b := lift(random()) mod 10000;
	c:F := 1;
	for i in 1..b repeat c := c * a;
	a^(b::Integer) = c;
}

print << "Testing mpf..." << newline;
sumitTest("inverse", inverse);
sumitTest("exponentiate", exponentiate);
print << newline;
#endif

