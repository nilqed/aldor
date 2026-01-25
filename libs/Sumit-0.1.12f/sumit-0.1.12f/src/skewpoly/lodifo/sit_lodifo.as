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
------------------------------ sit_lodifo.as ------------------------------
-- Copyright (c) Manuel Bronstein 1996
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1996-97
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{LinearOrdinaryDifferenceOperator}
\History{Manuel Bronstein}{23/12/94}{created}
\Usage{
import from \this(R, $\sigma$);\\
import from \this(R, $\sigma$, E);\\
}
\Params{
{\em R} & \astype{Ring} & A ring\\
{\em $\sigma$}&\astype{Automorphism} R &The automorphism to use for the action\\
{\em E} & \astype{Symbol} & The variable name (optional)\\
}
\Descr{\this0(R, $\sigma$, E) implements linear ordinary difference
operators with coefficients in R and shift $\sigma$.}
\begin{exports}
\category{\astype{LinearOrdinaryDifferenceOperatorCategory} R}\\
\end{exports}
#endif

macro {
	I	== MachineInteger;
	Z	== Integer;
	ARR	== PrimitiveArray;
	V	== Vector;
	RX	== DenseUnivariatePolynomial(R, avar);
	DR	== Derivation R;
	RID	== R pretend GcdDomain;
	F	== Fraction(RID);
}

LinearOrdinaryDifferenceOperator(R:Ring, sigma: Automorphism R,
	avar:Symbol==new()): LinearOrdinaryDifferenceOperatorCategory R ==
		UnivariateSkewPolynomial(R,RX,sigma,function(0$DR)$DR) add {};

-- This category is documented in sit_lodifo0.as
define LinearOrdinaryDifferenceOperatorCategory(R:Ring): Category ==
	LinearOrdinaryDifferenceOperatorCategory0 R with {
	default {
		if R has GcdDomain then {
			exteriorPower(L:%, N:Z):% == {
				import from I;
				assert(N > 0);
				zero? L or one?(n := machine N) => L;
				d := trailingDegree L;
				shift(exteriorPower0(shift(L, -d), n), d);
			}

			local exteriorPower0(L:%, n:I):% == {
				import from Boolean, Z, R;
				assert(n > 1);
				assert(~zero? L);
				assert(zero? trailingDegree L);
				m := machine(d := degree L);
				n > m => 1;
				n = m => {
					b := coefficient(L, 0)::%;
					assert(~zero? b);
					even? m => monom - b;
					monom + b;
				}
				extpow(L, n, m, leadingCoefficient L);
			}

			-- creating a new scope is necessary
			local extpow(L:%, n:I, m:I, p:R):% == {
				import from Z, Partial R, Automorphism R;
				import from ExteriorPower(RID, n, m);
				failed?(u := reciprocal p) => extpow0(L,n,m,p);
				pinv := retract u;
				a:ARR R := new m;
				for i in 0..prev m repeat
					a.i := - pinv * coefficient(L, i::Z);
				exteriorPower(a, function(shift$%))::%;
			}

			local lift(sigma:Automorphism R):Automorphism F == {
				morphism((f:F,n:Z):F +-> sigma(numerator f, n)_
						/ sigma(denominator f, n));
			}

			local extpow0(L:%, n:I, m:I, p:R):% == {
				import from Z, F, Automorphism F;
				import from ExteriorPower(F, n, m);
				a:ARR F := new m;
				for i in 0..prev m repeat
					a.i := - coefficient(L, i::Z) / p;
				vec2op exteriorPower(a, function lift(shift$%));
			}

			local vec2op(v:V F):% == {
				import from VectorOverFraction(RID, F);
				(a, w) := makeIntegral v;	-- w = a v
				w::%;
			}
		}
	}
}

