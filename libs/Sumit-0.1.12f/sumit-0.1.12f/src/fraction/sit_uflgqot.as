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
------------------------ sit_uflgqot.as ---------------------------
-- Copyright (c) Manuel Bronstein 1996
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1996
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{UnivariateFreeFiniteAlgebraOverFraction}
\History{Manuel Bronstein}{25/4/96}{created}
\Usage{import from \this(R, PR, Q, PQ)}
\Params{
{\em R} & \astype{IntegralDomain} & an integral domain\\
{\em PR} & \astype{UnivariateFreeFiniteAlgebra} R &
a univariate free finite algebra type over R\\
{\em Q} & \astype{FractionCategory} R & a fraction domain of R\\
{\em PQ} & \astype{UnivariateFreeFiniteAlgebra} R &
a univariate free finite algebra type over Q\\
}
\Descr{\this(R, PR, Q, PQ) provides useful conversions between
polynomials with integral and rational coefficients.}
\begin{exports}
\category{\astype{LinearCombinationFraction}(R, PR, Q, PQ)}\\
\end{exports}
#endif

UnivariateFreeFiniteAlgebraOverFraction(R:IntegralDomain,
	PR:UnivariateFreeFiniteAlgebra R,
	Q:FractionCategory R, PQ:UnivariateFreeFiniteAlgebra Q):
		LinearCombinationFraction(R, PR, Q, PQ) == add {
	-- All those functions use the fact that IntegralDomain's are
        -- commutative (if fractions of noncommutative domains are used
        -- one day, those functions must be recoded, as they will give
	-- incorrect results if R is not commutative).

	(x:Q) * (p:PR):PQ == {
		q:PQ := 0;
		for term in p repeat {
			(c, n) := term;
			q := add!(q, c * x, n);
		}
		q;
	}

	makeRational(p:PR):PQ == {
		import from Q;
		q:PQ := 0;
		for term in p repeat {
			(c, n) := term;
			q := add!(q, c::Q, n);
		}
		q;
	}

	if Q has FractionFieldCategory0 R then {
		normalize(p:PR):(R, PQ) == {
			import from Q;
			zero? p => (1, 0);
			a := leadingCoefficient p;
			q:PQ := monomial(1, degree p);
			for term in reductum p repeat {
				(c, n) := term;
				q := add!(q, c / a, n);
			}
			(a, q);
		}
	}

	local gcd?:Boolean		== R has GcdDomain;
	local denom(c:Q, n:Integer):R	== denominator c;

	local prod(l:List R):R == {
		r:R := 1;
		while ~empty? l repeat {
			r := times!(r, first l);
			l := rest l;
		}
		r;
	}

	makeIntegral(p:PQ):(R, PR) == {
		import from R, Q, List R, List Q;
		denoms := [denom term for term in p];
		d := { gcd? => lcm(denoms)$(R pretend GcdDomain); prod denoms; }
		q:PR := 0;
		for term in p repeat {
			(c, n) := term;
			q := add!(q, numerator(d * c), n);
		}
		(d, q);
	}

	if Q has FractionByCategory0 R then {
		makeIntegralBy(p:PQ):(Integer, PR) == {
			import from R, Q, List R, List Q;
			mu:Integer := 0;
			for term in p repeat {
				(c, n) := term;
				m:Integer := order(c)$Q;
				if m < mu then mu := m;
			}
			assert(mu <= 0);
			q:PR := 0;
			for term in p repeat {
				(c, n) := term;
				q := add!(q, numerator shift(c, -mu), n);
			}
			(mu, q);
		}
	}
}
