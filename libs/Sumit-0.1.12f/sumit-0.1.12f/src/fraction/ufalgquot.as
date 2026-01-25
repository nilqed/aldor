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
------------------------ ufalgquot.as ---------------------------
#include "sumit"

#if ASDOC
\thistype{UnivariateFreeAlgebraOverQuotient}
\History{Manuel Bronstein}{25/4/96}{created}
\Usage{import from \this(R, PR, Q, PQ)}
\Params{
{\em R} & IntegralDomain & an integral domain\\
{\em PR} & UnivariateFreeAlgebraCategory R &
a univariate free algebra type over R\\
{\em Q} & QuotientCategory R & a quotient of R\\
{\em PQ} & UnivariateFreeAlgebraCategory R &
a univariate free algebra type over Q\\
}
\Descr{\this(R, PR, Q, PQ) provides useful conversions between
polynomials with integral and rational coefficients.}
\begin{exports}
$*$: & (Q, PR) $\to$ PQ & product of a fraction by an integral polynomial\\
makeIntegral: & PQ $\to$ (R, PR) & conversion to an integral polynomial\\
makeRational: & PR $\to$ PQ & conversion to a rational polynomial\\
\end{exports}
\begin{exports}[if Q has QuotientFieldCategory0 R]
normalize: & PR $\to$ (R, PQ) & conversion to a monic rational polynomial\\
\end{exports}
#endif

UnivariateFreeAlgebraOverQuotient(R:IntegralDomain,
	PR:UnivariateFreeAlgebraCategory R,
	Q:QuotientCategory R,
	PQ:UnivariateFreeAlgebraCategory Q): with {
	*: (Q, PR) -> PQ;
#if ASDOC
\aspage{$*$}
\Usage{c~\name~p}
\Signature{(Q,PR)}{PQ}
\Params{
{\em c} & Q & A quotient\\
{\em p} & PR & A polynomial with integral coefficients\\
}
\Retval{Returns $c p$ as a polynomial with rational coefficients.}
#endif
	makeIntegral: PQ -> (R, PR);
#if ASDOC
\aspage{makeIntegral}
\Usage{(a, p) := \name~q}
\Signature{PQ}{(R, PR)}
\Params{ {\em q} & PQ & A polynomial with rational coefficients\\ }
\Retval{Returns $(a, p)$ such that $p = a q$ has integral coefficients.
If R is a GcdDomain, then $p$ is primitive.}
#endif
	makeRational: PR -> PQ;
#if ASDOC
\aspage{makeRational}
\Usage{\name~p}
\Signature{PR}{PQ}
\Params{ {\em p} & PR & A polynomial with integral coefficients\\ }
\Retval{Returns $p$ as a polynomial with rational coefficients.}
#endif
	if Q has QuotientFieldCategory0 R then {
		normalize: PR -> (R, PQ);
#if ASDOC
\aspage{normalize}
\Usage{(a, q) := \name~p}
\Signature{PR}{(R, PQ)}
\Params{ {\em p} & PR & A polynomial with integral coefficients\\ }
\Retval{Returns $(a, q)$ such that $p = a q$ and $q$ is monic and has
rational coefficients.}
#endif
	}
} == add {
	-- All those functions use the fact that IntegralDomain's are
        -- commutative (if quotients of noncommutative domains are used
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

	if Q has QuotientFieldCategory0 R then {
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

	local gcd?:Boolean == R has GcdDomain;

	local prod(l:List R):R == {
		r:R := 1;
		while ~empty? l repeat {
			r := times!(r, first l);
			l := rest l;
		}
		r;
	}

	makeIntegral(p:PQ):(R, PR) == {
		import from R, List R, List Q;
		denoms := [denominator c for c in coefficients p];
		d := { gcd? => lcm(denoms)$(R pretend GcdDomain); prod denoms; }
		q:PR := 0;
		for term in p repeat {
			(c, n) := term;
			q := add!(q, numerator(d * c), n);
		}
		(d, q);
	}
}
