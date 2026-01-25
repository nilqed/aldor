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
------------------------------ sit_linrect.as ------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro Z == Integer;

#if ALDOC
\thistype{LinearOrdinaryRecurrenceCategory}
\History{Manuel Bronstein}{5/6/2000}{created}
\Usage{ \this~R: Category }
\Params{ {\em R} & \astype{Ring} & A ring\\ }
\Descr{\this~R is the category of linear ordinary difference
operators with coefficients in R.}
\begin{exports}
\category{\astype{LinearOrdinaryDifferenceOperatorCategory} R}\\
\end{exports}
\begin{exports}[if $R$ has \astype{GcdDomain} then]
\asexp{sections}: & (\%, \astype{Integer}) $\to$ \astype{Array} \% Sections\\
\end{exports}
\begin{exports}[if $R$ has \astype{RationalRootRing} then]
% \asexp{initialConditions}:
% & (\%, \astype{Integer}) $\to$ \astype{List} Rx & Initial conditions\\
\asexp{singularities}:&\% $\to$ \astype{List} \astype{Integer} & Singularities\\
\end{exports}
#endif
define LinearOrdinaryRecurrenceCategory(R:Ring): Category ==
	LinearOrdinaryDifferenceOperatorCategory R with {
		if R has GcdDomain then sections: (%, Z) -> Array %;
#if ALDOC
\aspage{sections}
\Usage{\name(L, n)}
\Signature{(\%, \astype{Integer})}{\astype{Array} \%}
\Params{
{\em L} & \% & A difference operator\\
{\em n} & \astype{Integer} & A positive integer\\
}
\Retval{Returns $[L_0,\dots,L_{n-1}]$ of minimal orders
such that for any solution $y = (y_0,y_1,y_2,\dots)$ of $L y = 0$,
the sequences $y^{(i)} = (y_i, y_{i+n}, y_{i+2n},\dots)$ for $0 \le i < n$
satisfy $L_i y^{(i)} = 0$.}
#endif
		if R has RationalRootRing then singularities: % -> List Z;
#if ALDOC
\aspage{singularities}
\Usage{\name~L}
\Signature{\%}{\astype{List} \astype{Integer}}
\Params{ {\em L} & \% & A linear recurrence\\ }
\Retval{Returns the list of the integer roots
of the leading coefficient of $L$.}
#endif
}

LinearRecurrenceCategoryTools(R:GcdDomain,
	Re:LinearOrdinaryRecurrenceCategory R): with {
		section: (Re, Z) -> Re;
} == add {
	macro F == Fraction R;

	local lift(sigma:Automorphism R):Automorphism F == {
		morphism((f:F, n:Z):F +->
				sigma(numerator f,n) / sigma(denominator f,n));
	}

	section(L:Re, N:Z):Re == {
		import from R;
		assert(N > 0);
		zero? L or zero?(d := degree L) or one? N => L;
		unit?(a:=leadingCoefficient L) => monicSparseLeftMultiple(L, N);
		section1(L, N, lift(shift$Re));
	}

	local section1(L:Re, N:Z, sigma:Automorphism F):Re == {
		macro Fe == LinearOrdinaryDifferenceOperator(F, sigma);
		import from Fe;
		import from UnivariateFreeFiniteAlgebraOverFraction(R,Re,F,Fe);
		(a, LN) := makeIntegral sparseLeftMultiple(makeRational L, N);
		LN;
	}
}
