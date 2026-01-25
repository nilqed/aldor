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
----------------------------- sit_algext.as ---------------------------------
-- Copyright (c) Manuel Bronstein 1996
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1996-97
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{UnivariatePolynomialQuotient}
\History{Manuel Bronstein}{27/12/96}{created}
\Usage{ \this(R, Rx):Category }
\Params{
{\em R} & \astype{CommutativeRing} & The coefficient ring of the polynomials\\
{\em Rx} & \astype{UnivariatePolynomialCategory0} R & The type of the modulus\\
}
\Descr{\this(R, Rx) is the category of extensions of $R$ of the form
$Rx / (p)$ for some $p \in Rx$, not necessarily irreducible.
Use \astype{SimpleAlgebraicExtensionCategory} for extensions where the
modulus is known to be irreducible.}
\begin{exports}
\category{\astype{Algebra} R}\\
\category{\astype{CommutativeRing}}\\
\asexp{compose}: & \% $\to$ \% $\to$ \% & Modular composition\\
\asexp{definingPolynomial}: & $\to$ Rx & Defining polynomial\\
\asexp{lift}: & \% $\to$ Rx & Conversion to a polynomial\\
\asexp{reduce}: & Rx $\to$ \% & Reduction of a polynomial\\
\end{exports}
\begin{exports}[if R has \astype{FiniteCharacteristic} then]
\category{\astype{FiniteCharacteristic}}\\
\end{exports}
\begin{exports}[if R has \astype{FiniteSet} then]
\category{\astype{FiniteSet}}\\
\end{exports}
\begin{exports}[if R has \astype{RationalRootRing} then]
\category{\astype{RationalRootRing}}\\
\end{exports}
#endif

macro {
	Z == Integer;
	POLY == UnivariatePolynomialCategory0;
}

define UnivariatePolynomialQuotient(R:CommutativeRing, Rx: POLY R):
	Category == Join(CommutativeRing, Algebra R) with {
		if R has FiniteSet then FiniteSet;
		if R has FiniteCharacteristic then FiniteCharacteristic;
		if R has RationalRootRing then RationalRootRing;
		compose: % -> % -> %;
#if ALDOC
\aspage{compose}
\Usage{\name(p)(q)}
\Params{ {\em p, q} & \% & Polynomials\\ }
\Retval{Returns
$$
q(p) = \sum_{i=0}^n a_i p^i
$$
where $q = \sum_{i=0}^n a_i x^i$.}
\Remarks{If you want to compute
$q_1(p),\dots,q_k(p)$ for several $q_i$'s, use the curried version
as follows: {\tt f := compose p; for i in 1..k repeat r.i := f(q.i); },
since the various calls to {\tt f} will share a table of powers of $p$.}
#endif
		definingPolynomial: Rx;
#if ALDOC
\aspage{definingPolynomial}
\Usage{\name}
\Signature{}{Rx}
\Retval{Returns the polynomial $p$ such that the extension is $Rx/(p)$.}
#endif
		lift: % -> Rx;
#if ALDOC
\aspage{lift}
\Usage{\name~q}
\Signature{\%}{Rx}
\Params{ {\em q} & \% & An element of the algebraic extension\\ }
\Retval{Returns $q$ as an element of $Rx$.}
#endif
		reduce: Rx -> %;
#if ALDOC
\aspage{reduce}
\Usage{\name~q}
\Signature{Rx}{\%}
\Params{ {\em q} & Rx & A polynomial\\ }
\Retval{Returns the remainder of $q$ modulo $p$ as an element of $Rx / (p)$.}
#endif
		value: (P:POLY %) -> (P, Z, Z) -> %;
#if ALDOC
\aspage{value}
\Usage{\name(P)(p, n, d)}
\Signature{(P:\astype{UnivariatePolynomialCategory0} \%)}
{(P, \astype{Integer}, \astype{Integer}) $\to$ \%}
\Params{
{\em P} & \astype{UnivariatePolynomialCategory0} \% & A polynomial type\\
{\em p} & P & A polynomial\\
{\em n} & \astype{Integer} & A numerator\\
{\em d} & \astype{Integer} & A nonzero denominator\\
}
\Retval{Returns $d^e p(n/d)$ where $e$ is the smallest nonnegative exponent
such that $d^e p(n/d)$ is an element of the extension.}
#endif
		default {
			if R has FiniteSet then {
				#:Z == {
					import from Rx;
					(#$R)^(degree definingPolynomial);
				}

				-- storing is by increasing degree:
				--  degree 0 = index$R
				--  degree 1 = #$R*index(coeff1) + index(coeff0)
				--  etc.
				index(x:%):Z == {
					import from R;
					p:Rx := lift x;
					zero? p => 0;
					r := #$R;
					assert(r > 0);
					v := index leadingCoefficient p;
					for i in prev degree p .. 0 by -1 repeat
						v := r*v+index coefficient(p,i);
					v;
				}

				lookup(n:Z):% == {
					import from R, Rx;
					m := n mod (#$%);
					assert(m >= 0);
					r := #$R;
					assert(r > 0);
					d := degree definingPolynomial;
					p := monomial(1, d);
					i:Z := 0;
					while m > 0 repeat {
						(m, a) := divide(m, r);
						p := add!(p, lookup a, i);
						i := next i;
					}
					p := add!(p, -1, d);	-- remove x^d
					reduce p;
				}
			}

			-- returns d^{degree p} p(n/d)
			local qvalue(P:POLY %, p:P, n:Z, d:Z):% == {
				import from Boolean, R;
				assert(~unit?(d::R));
				v:% := 0;
				g := degree p;
				for term in p repeat {
					(c, e) := term;
					if ~(zero? c) then
						v := add!(v, n^e * d^(g-e) * c);
				}
				v;
			}

			value(P:POLY %):(P, Z, Z) -> % == {
				(p:P, n:Z, d:Z):% +-> {
					import from R, Partial R;
					u := reciprocal(d::R);
					failed? u => qvalue(P, p, n, d);
					d1 := retract u;
					p((n * d1)::%);
				}
			}
		}
}

