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
----------------------------- spf.as ----------------------------------
#include "sumit"

macro {
	Z == SingleInteger;
	POLY == UnivariatePolynomialCategory0;
}

#if ASDOC
\thistype{SmallPrimeField}
\History{Manuel Bronstein}{6/7/94}{created}
\Usage{import from \this~p}
\Params{ {\em p} & SingleInteger & The characteristic\\ }
\Descr{\this~p implements the finite field $\ZZ_p$ where $p$ is a word-size
prime.}
\begin{exports}
\category{PrimeFieldCategory}\\
\end{exports}
#endif

-- TEMPORARY: NEEDS with {} (BUGS 1035/1036)
-- SmallPrimeField(p:Z): SmallPrimeFieldCategory == {
SmallPrimeField(p:Z): SmallPrimeFieldCategory with {} == {
        -- sanity checks on the parameters
        ASSERT(p > 1);

	add {
	macro Rep == Z;

	import from Rep;

	local maxhalf:Z				== maxPrime$HalfWordSizePrimes;
	0:%					== per 0;
	1:%					== per 1;
	local p1:Integer			== prev(p)::Integer;
	karatsubaCutoff:Z			== 20;
	fftCutoff:Z				== 400;
	zero?(a:%):Boolean			== zero? rep a;
	characteristic:Integer			== p::Integer;
	(a:%) = (b:%):Boolean			== rep a = rep b;
	lift(a:%):Z				== rep a;
	reduce(a:Z):%				== per(a rem p);
	(a:%) + (b:%):%				== per mod_+(rep a, rep b, p);
	(a:%) / (b:%):%				== per mod_/(rep a, rep b, p);
	inv(a:%):%				== per mod_/(1, rep a, p);
	-(a:%):%			== { zero? a => a; per(p - rep a); }

	if p > maxhalf then {
		(a:%) * (b:%):%			== per mod_*(rep a, rep b, p);
	} else {
		(a:%) * (b:%):%			== per((rep(a) * rep(b)) rem p);
	}

	(a:%)^(n:Integer):% == {
		zero? a => 0;
		one? a => a;
		m:Z := retract(n mod p1);
		per mod_^(rep a, m, p);
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
---------------------- test spf.as --------------------------
#include "sumittest"

macro F == SmallPrimeField 10007;

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

print << "Testing spf..." << newline;
sumitTest("sum", sum);
sumitTest("inverse", inverse);
sumitTest("exponentiate", exponentiate);
print << newline;
#endif

