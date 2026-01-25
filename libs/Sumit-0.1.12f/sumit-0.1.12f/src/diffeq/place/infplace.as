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
------------------------------ infplace.as --------------------
#include "sumit"

#if ASDOC
\thistype{RationalInfinity}
\History{Manuel Bronstein}{23/5/95}{created}
\Usage{import from \this(R, P)}
\Params{
{\em R} & IntegralDomain & The coefficient ring of the polynomials\\
{\em P} & UnivariatePolynomialCategory R & A polynomial type over R\\
}
\Descr{\this(R, P) provides the localisations of the elements of
P at $x = \infty$.}
\begin{exports}
\category{DifferentialPlace(P, R)}\\
\end{exports}
#endif

RationalInfinity(R:IntegralDomain, P:UnivariatePolynomialCategory R):
	DifferentialPlace(P, R) == add {
		x:P					== monom;
		orderOf(p:P):Integer			== - degree p;
		normal?(D:Derivation P):Boolean		== one? D x;
		orderDrop(D:Derivation P):Integer	== next orderOf D x;
		leadingCoefficient(p:P):R	== leadingCoefficient(p)$P;
		residue(D:Derivation P):R	== - leadingCoefficient(D x)$P;

		orderOf(p:P, m:Integer):Partial Integer == {
			zero? p or (n := orderOf p) > m => failed;
			[n];
		}

		value(p:P):R == {
			import from Integer;
			zero? p => 0;
			ASSERT(zero? degree p);
			leadingCoefficient(p)$P;
		}
}

#if ASDOC
\thistype{RationalInfinityQ}
\History{Manuel Bronstein}{23/5/95}{created}
\Usage{import from \this(F, P)}
\Params{
{\em F} & SumitField & The coefficient field of the polynomials\\
{\em P} & UnivariatePolynomialCategory F & A polynomial type over F\\
}
\Descr{\this(F, P) provides the localisations of the elements of
Quotient~P at $x = \infty$.}
\begin{exports}
\category{DifferentialPlace(Quotient P, F)}\\
\end{exports}
#endif

RationalInfinityQ(F:SumitField, P:UnivariatePolynomialCategory F):
	DifferentialPlace(Quotient P, F) == add {
		macro Q == Quotient P;

		x:P					== monom;
		xq:Q					== x::Q;
		normal?(D:Derivation Q):Boolean		== one? D xq;
		orderDrop(D:Derivation Q):Integer	== next orderOf D xq;
		residue(D:Derivation Q):F == - leadingCoefficient(D(xq) / xq);

		orderOf(p:Q):Integer ==
			degree(denominator p) - degree(numerator p);

		orderOf(p:Q, m:Integer):Partial Integer == {
			zero? p or (n := orderOf p) > m => failed;
			[n];
		}

		leadingCoefficient(p:Q):F == {
			leadingCoefficient(numerator p) /
				leadingCoefficient(denominator p);
		}

		value(p:Q):F == {
			import from Integer, Partial Integer;
			failed?(u := orderOf(p, 0)) => 0;
			ASSERT(zero? retract u);
			leadingCoefficient p;
		}
}

