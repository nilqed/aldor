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
--------------------------------- modpgcd.as --------------------------------
#include "sumit"

#if ASDOC
\thistype{ModulopUnivariateGcd}
\History{Manuel Bronstein}{24/7/98}{created}
\Usage{import from \this}
\Descr{\this~provides an implementation of an inplace gcd for polynomials
modulo a machine prime.}
\begin{exports}
gcd!: & (ARR Z, Z, ARR Z, Z, Z, Z) $\to$ (ARR Z, Z, Z) & in-place gcd\\
\end{exports}
\begin{aswhere}
Z &==& SingleInteger\\
ARR &==& PrimitiveArray\\
\end{aswhere}
#endif

macro {
	SI  == SingleInteger;
	ARR == PrimitiveArray;
}

ModulopUnivariateGcd: with {
	gcd!:(ARR SI, SI, ARR SI, SI, SI, SI) -> (ARR SI, SI, SI);
	gcd!:(ARR SI, SI, ARR SI, SI, SI, SI, ARR SI, ARR SI) -> (ARR SI,SI,SI);
#if ASDOC
\aspage{gcd!}
\Usage{\name(a, n, b, m, $\alpha$, p)\\
\name(a, n, b, m, $\alpha$, p, $[l_1,\dots,l_{p-1}], [e_1,\dots,e_{p-1}]$)}
\Signatures{
\name: (ARR Z, Z, ARR Z, Z, Z) $\to$ (ARR Z, Z, Z)\\
\name: (ARR Z, Z, ARR Z, Z, Z, ARR Z, ARR Z) $\to$ (ARR Z, Z, Z)\\
}
\begin{aswhere}
Z &==& SingleInteger\\
ARR &==& PrimitiveArray\\
\end{aswhere}
\Params{
{\em a,b} & PrimitiveArray SingleInteger & polynomials modulo p\\
{\em n,m} & SingleInteger & their degrees\\
$\alpha$ & SingleInteger & a leading coefficient\\
{\em p} & SingleInteger & a prime\\
$[l_1,\dots,l_{p-1}]$ & PrimitiveArray SingleInteger & log table\\
$[e_1,\dots,e_{p-1}]$ & PrimitiveArray SingleInteger & exp table\\
}
\Descr{
Given 2 polynomials stored in $a$ and $b$ of degrees $n$ and $m$ respectively,
computes a $\gcd(a,b)$ in $F_p[x]$ with leading coefficient $\alpha$.
Requires $n \ge m$ and that the polynomials are stored leading coefficient
first. Returns the degree of the gcd and its starting index in the array.
}
\Remarks{
The result can be stored in either $a$ or $b$, so the function also returns
the appropriate array. Note that both $a$ and $b$ are destroyed.
The last 2 optional arrays are such that $g^{l_i} = i$ and $e_i = g^{i-1}$
where $g$ is a primitive root for the multiplicative group modulo $p$.
They are used for fast multiplication if provided.
}
#endif
} == add {
	local maxhalf:SI	== maxPrime$HalfWordSizePrimes;
	local maxint:SI		== max$SI;

#if ASTRACE
	local prt(str:String, a:ARR SI, n:SI, s:SI):() == {
		print << str << " = ";
		for i in 0..n repeat print << a(s+i) << " ";
		print << newline;
	}
#else
	local prt(str:String, a:ARR SI, n:SI, s:SI):() == {};
#endif

	gcd!(a:ARR SI, n:SI, b:ARR SI, m:SI, lc:SI, p:SI):(ARR SI, SI, SI) == {
		TRACE("gcd!:p = ", p);
		prt("gcd!:a", a, n, 1);
		prt("gcd!:b", b, m, 1);
		assert(n >= m); assert(p > 1);
		p > maxhalf => fullgcd!(a, n, b, m, lc, p);
		-- from normalized inputs, the first k loops cannot overflow
		k := prev(maxint quo (prev(p)^2));
		TRACE("gcd!:k = ", k);
		k > 10 => halfgcd!(a, n, b, m, lc, k, p);
		halfgcd!(a, n, b, m, lc, p);
	}

	gcd!(a:ARR SI, n:SI, b:ARR SI, m:SI, lc:SI, p:SI, log:ARR SI,
		exp:ARR SI):(ARR SI, SI, SI) == {
			prt("gcd!:a", a, n, 1);
			prt("gcd!:b", b, m, 1);
			prt("gcd!:log", log, p-2, 1);
			prt("gcd!:exp", log, p-2, 1);
			assert(n >= m); assert(p > 1);
			gcd!(a, n, b, m, lc, p, log, exp, prev p);
	}

-- Those 3 files contain similar code with 3 different product functions
-- (the product is not passed as parameter because the function-call
--  overhead is too high, and this would prevent inlining)
#include "fullgcd.as"
#include "halfgcd.as"
#include "loggcd.as"
}
