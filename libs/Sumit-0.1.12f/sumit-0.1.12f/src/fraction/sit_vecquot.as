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
------------------------ sit_vecquot.as ---------------------------
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I == MachineInteger;
	V == Vector;
}

#if ALDOC
\thistype{VectorOverFraction}
\History{Manuel Bronstein}{13/7/98}{created}
\Usage{import from \this(R, Q)}
\Params{
{\em R} & \astype{IntegralDomain} & an integral domain\\
{\em Q} & \astype{FractionCategory} R & a fraction domain over R\\
}
\Descr{\this(R, Q) provides useful conversions between
vectors with integral and rational coefficients.}
\begin{exports}
\category{
\astype{LinearCombinationFraction}(R,\astype{Vector} R,Q,\astype{Vector} Q)}\\
\end{exports}
#endif

VectorOverFraction(R:IntegralDomain, Q:FractionCategory R):
	LinearCombinationFraction(R, V R, Q, V Q) == add {
	local gcd?:Boolean == R has GcdDomain;

	-- Most of those functions use the fact that IntegralDomain's are
        -- commutative (if fractions of noncommutative domains are used
        -- one day, those functions must be recoded, as they will give
	-- incorrect results if R is not commutative).

	(x:Q) * (v:V R):V Q == {
		import from I;
		w:V Q := zero(n := #v);
		for i in 1..n repeat w.i := v.i * x;
		w;
	}

	makeRational(v:V R):V Q == {
		import from I, Q;
		w:V Q := zero(n := #v);
		for i in 1..n repeat w.i := (v.i)::Q;
		w;
	}

	if Q has FractionFieldCategory0 R then {
		normalize(v:V R):(R, V Q) == {
			import from I, Q;
			w:V Q := zero(n := #v);
			zero? n => (1, w);
			a := v.1;
			for i in 1..n repeat w.i := v.i / a;
			(a, w);
		}
	}

	local prod(l:List R):R == {
		r:R := 1;
		while ~empty? l repeat {
			r := times!(r, first l);
			l := rest l;
		}
		r;
	}

	makeIntegral(w:V Q):(R, V R) == {
		import from I, R, Q, List R;
		v:V R := zero(n := #w);
		l:List R := [denominator(w.i) for i in 1..n];
		d := { gcd? => lcm(l)$(R pretend GcdDomain); prod l; }
		for i in 1..n repeat v.i := numerator(d * w.i);
		(d, v);
	}

	if Q has FractionByCategory0 R then {
		macro QQ == (Q pretend FractionByCategory0 R);
		makeIntegralBy(w:V Q):(Integer, V R) == {
			import from I, Boolean, Q;
			v:V R := zero(n := #w);
			mu:Integer := 0;
			for j in 1..n | ~zero?(b := w.j) repeat {
				m:Integer := order(b)$QQ;
				if m < mu then mu := m;
			}
			assert(mu <= 0);
			for i in 1..n repeat v.i := numerator shift(w.i, -mu);
			(mu, v);
		}
	}
}
