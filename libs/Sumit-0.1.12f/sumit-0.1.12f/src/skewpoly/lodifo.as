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
------------------------------ lodifo.as ------------------------------
#include "sumit"

#if ASDOC
\thistype{LinearOrdinaryDifferenceOperatorCategory}
\History{Manuel Bronstein}{13/08/96}{created}
\Usage{ \this~R: Category }
\Params{ {\em R} & CommutativeRing & A commutative ring\\ }
\Descr{\this~R is the category of linear ordinary difference
operators with coefficients in R.}
\begin{exports}
\category{UnivariateSkewPolynomialCategory R}\\
apply: & (\%, R) $\to$ R & Applies an operator to an element of R\\
\end{exports}
#endif
LinearOrdinaryDifferenceOperatorCategory(R:CommutativeRing): Category ==
	UnivariateSkewPolynomialCategory R with {
		apply: (%, R) -> R;
#if ASDOC
\aspage{apply}
\Usage{ \name(L, x)\\L~x }
\Signature{(\%, R)}{R}
\Params{
{\em L} & \% & A difference operator\\
{\em x} & R & A ring element\\
}
\Retval{Returns
$$
L x = \sum_{i=0}^n a_i \sigma^i x
$$
where $L = \sum_{i=0}^n a_i \sigma^i$.}
#endif
}

#if ASDOC
\thistype{LinearOrdinaryDifferenceOperator}
\History{Manuel Bronstein}{23/12/94}{created}
\Usage{
import from \this(R, $\sigma$);\\
import from \this(R, Rx);\\
import from \this(R, $\sigma$, n);\\
import from \this(R, Rx, n);\\
}
\Params{
{\em R} & CommutativeRing & A commutative ring\\
{\em $\sigma$} & Automorphism R & The automorphism to use for the action\\
{\em Rx} & UnivariatePolynomialCategory R & A polynomial ring over R\\
{\em n} & String & The variable name (optional)\\
}
\Descr{\this(R, $\sigma$, n) implements linear ordinary difference
operators with coefficients in R and shift $\sigma$, while
\this(R, Rx, n) implements linear ordinary difference operators with
coefficients in Rx and shift $p(n) \to p(n+1)$.}
\begin{exports}
\category{LinearOrdinaryDifferenceOperatorCategory R (resp.~Rx)}\\
\end{exports}
\begin{exports}[for coefficients in $Rx$]
initialConditions: & (\%, Integer) $\to$ List Rx & initial conditions\\
\end{exports}
\begin{exports}[for coefficients in $Rx$, if $R$ has RationalRootRing then]
singularities: & \% $\to$ List Integer & singularities\\
\end{exports}
#endif

macro {
	Symbol	== String;
	anon	== "\sigma";
	ARR	== Array;
	I	== SingleInteger;
	Z	== Integer;
-- TEMPORARY: BUG1135
--	DUSP	== DenseUnivariateSkewPolynomial(R, sigma, function 0, avar);
	DR	== Derivation R;
	DUSP	==DenseUnivariateSkewPolynomial(R,sigma,function(0$DR)$DR,avar);
}

LinearOrdinaryDifferenceOperator(R:CommutativeRing, sigma: Automorphism R,
	avar:Symbol == anon): LinearOrdinaryDifferenceOperatorCategory R == {
-- TEMPORARY: BUG1135
--		import from Derivation R;

		DUSP add {
			macro Rep == DUSP;
			import from Rep;

			apply(p:%, r:R):R == apply(rep p, 1, r);
		}
}

LinearOrdinaryDifferenceOperator(R:CommutativeRing,
	Rx:UnivariatePolynomialCategory R,
	avar:Symbol == anon): LinearOrdinaryDifferenceOperatorCategory Rx
-- TEMPORARY: 1.1.10 COMPILER BUG
	-- avar:Symbol == anon): LinearOrdinaryDifferenceOperatorCategory Rx with {
		-- if R has RationalRootRing then singularities: % -> List Z;
#if ASDOC
\aspage{singularities}
\Usage{\name~L}
\Signature{\%}{List Integer}
\Params{ {\em L} & \% & A difference operator\\ }
\Retval{Returns the list of the integer roots
of the leading coefficient of $L$.}
#endif
	-- } == {
	== {
		import from R, Automorphism Rx;

		local shift(p:Rx, n:Integer):Rx == p(monom + n::Rx);

		LinearOrdinaryDifferenceOperator(Rx, morphism shift, avar);
-- TEMPORARY: 1.1.10 COMPILER BUG
#if NOMORECOMPILERBUG
		LinearOrdinaryDifferenceOperator(Rx, morphism shift, avar) add {
		if R has RationalRootRing then {
			singularities(L:%):List Integer == {
				import from Rx, RationalRoot, List RationalRoot;
				[integerValue r for r in
					integerRoots leadingCoefficient L];
			}
		}
	}
#endif
}
