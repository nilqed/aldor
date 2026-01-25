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
------------------------------ sit_linrec.as ------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{LinearOrdinaryRecurrence}
\History{Manuel Bronstein}{5/6/2000}{created}
\Usage{
import from \this(R, Rx);\\
import from \this(R, Rx, E);\\
}
\Params{
{\em R} & \astype{Ring} & A ring\\
{\em Rx} & \astype{UnivariatePolynomialCategory} R & A polynomial ring over R\\
{\em E} & \astype{Symbol} & The variable name (optional)\\
}
\Descr{\this(R, Rx, E) implements linear ordinary difference operators with
coefficients in Rx and shift $p(n) \to p(n+1)$.}
\begin{exports}
\category{\astype{LinearOrdinaryRecurrenceCategory} Rx}\\
\end{exports}
#endif

macro {
	I  == MachineInteger;
	Z  == Integer;
	Rx == Fraction RX;
}

LinearOrdinaryRecurrence(R:Ring, RX:UnivariatePolynomialCategory R,
	avar:Symbol == new()): LinearOrdinaryRecurrenceCategory RX == {

	import from R, Automorphism RX;

	local sig(p:RX, n:Z):RX == { zero? n => p; translate(p, (-n)::R); }

	-- TEMPORARY: 1.1.12p6 COMPILE-TIME BUG WITH 'morphism sig'
	-- LinearOrdinaryDifferenceOperator(RX, morphism sig, avar) add {
	local sigma:Automorphism RX == morphism sig;
	LinearOrdinaryDifferenceOperator(RX, sigma, avar) add {
		shift:Automorphism RX == morphism sig;

		if R has RationalRootRing then {
			singularities(L:%):List Z == {
				import from RX, FractionalRoot Z;
				[integralValue r for r in
					integerRoots leadingCoefficient L];
			}
		}

		if R has GcdDomain then {
			local tau(m:Z):Z -> RX -> RX == {
				mx:RX := monomial(m::R, 1);
				(i:Z):RX -> RX +-> {
					(p:RX):RX +-> sig(p, i)(mx)
				}
			}

			sections(L:%, n:Z):Array % == {
				import from I;
				import from LinearRecurrenceCategoryTools(RX,%);
				LL := section(L, n);
				taun := tau n;
				[map(taun i)(LL) for i in 0..prev n];
			}
		}
	}
}

#if ALDOC
\thistype{LinearOrdinaryRecurrenceQ}
\History{Manuel Bronstein}{31/7/2000}{created}
\Usage{
import from \this(R, Rx);\\
import from \this(R, Rx, E);\\
}
\Params{
{\em R} & \astype{GcdDomain} & An integral domain\\
{\em Rx} & \astype{UnivariatePolynomialCategory} R & A polynomial ring over R\\
{\em E} & \astype{Symbol} & The variable name (optional)\\
}
\Descr{\this(R, Rx, E) implements linear ordinary difference operators with
coefficients in the fraction field of Rx and shift $f(n) \to f(n+1)$.}
\begin{exports}
\category{\astype{LinearOrdinaryRecurrenceCategory} \astype{Fraction} Rx}\\
\end{exports}
#endif

LinearOrdinaryRecurrenceQ(R:GcdDomain, RX:UnivariatePolynomialCategory R,
	avar:Symbol == new()): LinearOrdinaryRecurrenceCategory Rx == {

	import from R, Automorphism Rx;

	local sig(p:Rx, n:Z):Rx == {
		import from RX;
		zero? n => p;
		nn := (-n)::R;
		translate(numerator p, nn) / translate(denominator p, nn);
	}

	-- TEMPORARY: 1.1.12p6 COMPILE-TIME BUG WITH 'morphism sig'
	-- LinearOrdinaryDifferenceOperator(Rx, morphism sig, avar) add {
	local sigma:Automorphism Rx == morphism sig;
	LinearOrdinaryDifferenceOperator(Rx, sigma, avar) add {
		shift:Automorphism Rx == morphism sig;

		if R has RationalRootRing then {
			singularities(L:%):List Z == {
				import from Boolean, RX, Rx, FractionalRoot Z;
				l:List Z := empty;
				for term in L repeat {
					(f, n) := term;
					d := denominator f;
					for r in integerRoots d repeat {
						n := integralValue r;
						if ~member?(n, l) then
								l := cons(n, l);
					}
				}
				l;
			}
		}

		if R has GcdDomain then {
			local tau(m:Z):Z -> Rx -> Rx == {
				mx:RX := monomial(m::R, 1);
				(i:Z):Rx -> Rx +-> {
					(f:Rx):Rx +-> {
						g := sig(f, i);
						numerator(g)(mx) / _
							denominator(g)(mx);
					}
				}
			}

			sections(L:%, n:Z):Array % == {
				import from I;
				import from LinearRecurrenceCategoryTools(Rx,%);
				LL := section(L, n);
				taun := tau n;
				[map(taun i)(LL) for i in 0..prev n];
			}
		}
	}
}

