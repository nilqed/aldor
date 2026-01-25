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
------------------------ sit_qotfct0.as ---------------------------
-- Copyright (c) Laurent Bernardin 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{FractionFieldCategory0}
\History{Laurent Bernardin}{1/12/94}{created}
\History{Manuel Bronstein}{25/5/95}
{extracted the category from the type in order to create RationalCategory}
\History{Manuel Bronstein}{21/9/95}{added UnivariateGcdRing and gcd lifting}
\Usage{\this~R: Category}
\Params{ {\em R} & \astype{IntegralDomain} & an integral domain\\ }
\Descr{\this~R is the category of the fraction fields of R.}
\begin{exports}
\category{\astype{Field}}\\
\category{\astype{FractionCategory} R}\\
\asexp{/}: & (R,R) $\to$ \% & Quotient of two ring elements\\
\end{exports}
\begin{exports}[if $R$ has \astype{CharacteristicZero} then]
\category{\astype{QRing}}\\
\end{exports}
#endif

define FractionFieldCategory0(R: IntegralDomain): Category ==
	Join(Field, FractionCategory R) with {
	if R has CharacteristicZero then QRing;
	/:		(R, R) -> %;
#if ALDOC
\aspage{/}
\Usage{n~\name~d}
\Signature{(R,R)}{\%}
\Params{
{\em n} & R & An element of the ring.\\
{\em d} & R & A nonzero element of the ring.\\
}
\Retval{Returns the quotient {\em n} over {\em d}.}
#endif
	default {
		import from R;

		(p:R) * (a:%):% == (p * numerator a) / (denominator a);
		random():%	== random()$R / random()$R;

		relativeSize(a:%):MachineInteger ==
			relativeSize(numerator a) + relativeSize(denominator a);

		if R has CharacteristicZero then inv(n:Integer):% == 1 / (n::R);

		(a:%) + (b:%):% == {
			(numerator a * denominator b +
				denominator a * numerator b) /
					(denominator a * denominator b);
		}
	
		(a:%) * (b:%):% == {
			(numerator a * numerator b) /
				(denominator a * denominator b);
		}

		(a:%) = (b:%):Boolean == {
			numerator a * denominator b =
				denominator a * numerator b;
		}

--		if R has OrderedRing then {
--			(a:%) > (b:%):Boolean == {
--				numerator(a) * denominator(b) >
--					numerator(b) * denominator(a);
--			}
--		}

		lift(D:Derivation R):Derivation % == {
			import from Integer;
			derivation {(f:%):% +-> {
				n := numerator f; d := denominator f;
				D(n) / d - n * (D(d) / d^2);
			} }
		}

		if R has FiniteCharacteristic then {
			pthPower(a:%):% ==
				pthPower(numerator a) / pthPower(denominator a);
		}
	}
}		
