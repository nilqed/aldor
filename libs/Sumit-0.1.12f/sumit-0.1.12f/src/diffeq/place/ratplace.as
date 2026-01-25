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
------------------------------ ratplace.as --------------------
#include "sumit"

#if ASDOC
\thistype{RationalPlace}
\History{Manuel Bronstein}{31/1/95}{created}
\Usage{import from \this(R, P, a)}
\Params{
{\em R} & IntegralDomain & The coefficient ring of the polynomials\\
{\em P} & UnivariatePolynomialCategory R & A polynomial type over R\\
{\em a} & R & The localization point\\
}
\Descr{\this(R, P, a) provides the localisations of the elements of
P at $x = a$.}
\begin{exports}
\category{DifferentialPlace(P, R)}\\
\end{exports}
#endif

RationalPlace(R:IntegralDomain, P:UnivariatePolynomialCategory R, a:R):
	DifferentialPlace(P, R) == add {
		local center:P				== monom - a::P;
		local nu:P -> Integer			== order center;
		local nuquo:P -> (Integer, P)		== orderquo center;
		orderOf(p:P):Integer			== nu p;
		value(p:P):R				== p a;
		orderDrop(D:Derivation P):Integer	== prev nu D center;
		normal?(D:Derivation P):Boolean	== ~zero?(value(D center));
		residue(D:Derivation P):R == leadingCoefficient(D center)$%;

		leadingCoefficient(p:P):R == {
			zero? p => 0;
			(n, p) := nuquo p;
			value p;
		}

		orderOf(p:P, m:Integer):Partial Integer == {
			zero? p or (n := orderOf p) > m => failed;
			[n];
		}
}

#if ASDOC
\thistype{RationalPlace1}
\History{Manuel Bronstein}{10/12/96}{created}
\Usage{import from \this(R, P, a, b)}
\Params{
{\em R} & IntegralDomain & The coefficient ring of the polynomials\\
{\em P} & UnivariatePolynomialCategory R & A polynomial type over R\\
{\em a, b} & R & Numerator and denominator of the center\\
}
\Descr{\this(R, P, a, b) provides the localisations of the elements of
P at $x = b/a$, also when a is not a unit in R. If R is a Gcd domain,
then a and b should be coprime. For efficiency, use {\tt RationalPlace}
when a is a unit in R.}
\begin{exports}
\category{DifferentialPlace(P, QuotientBy(R, a))}\\
\end{exports}
#endif

macro {
	-- E  == NonNormalizingQuotientBy(R, a);
	E  == QuotientBy(R, a, false);
	Ex == SparseUnivariatePolynomial E;
}
-- place centered at b/a, a shouldn't divide b in R
-- a and b should be coprime if R is a gcd domain
RationalPlace1(R:IntegralDomain, P:UnivariatePolynomialCategory R, a:R, b:R):
	DifferentialPlace(P, E) == {
		-- sanity checks on the parameters
		ASSERT(~zero? a);
		ASSERT(~unit? a);

		add {
		local center:P == { import from Integer; monomial(a,1) - b::P }
		local nu:P -> Integer		== order center;
		local nuquo:P -> (Integer, P)	== orderquo center;
		orderOf(p:P):Integer		== nu p;
		orderDrop(D:Derivation P):Integer	== prev nu D center;

		normal?(D:Derivation P):Boolean	== {
			import from E;
			~zero?(value(D center));
		}

		value(p:P):E == {
			(q, v) := horner p;
			v;
		}

		local horner(p:P):(Ex, E) == {
			import from Integer, Ex;
			zero? p => (0, 0);
			v := leadingCoefficient(p)::E;
			q:Ex := 0;
			for i in prev degree p .. 0 by -1 repeat {
				q := add!(q, v, i);
				v := shift(b * v, -1) + coefficient(p, i)::E;
			}
			(q, v);
                }

		local lcoeff(p:Ex):E == {
			import from E;
			nu:Integer := order leadingCoefficient p;
			-- compute the minimum order
			for term in reductum p repeat {
				(c, e) := term;
				n:Integer := order c;
				if n < nu then nu := n;
			}
			q:P := 0;
			for term in p repeat {
				(c, e) := term;
				q := add!(q, numerator shift(c, -nu), e);
			}
			shift(leadingCoefficient(q)$%, nu);
		}

		leadingCoefficient(p:P):E == {
			zero? p => 0;
			(n, p) := nuquo p;
			value p;
		}

		orderOf(p:P, m:Integer):Partial Integer == {
			zero? p or (n := orderOf p) > m => failed;
			[n];
		}

		residue(D:Derivation P):E == {
			(q, r) := horner(D center);
			zero? r => lcoeff q;
			r;
		}
	}
}

#if ASDOC
\thistype{RationalPlaceQ}
\History{Manuel Bronstein}{23/5/95}{created}
\Usage{import from \this(F, P, a)}
\Params{
{\em F} & SumitField & The coefficient field of the polynomials\\
{\em P} & UnivariatePolynomialCategory F & A polynomial type over F\\
{\em a} & F & The localization point\\
}
\Descr{\this(F, P, a) provides the localisations of the elements of
Quotient~P at $x = a$.}
\begin{exports}
\category{DifferentialPlace(Quotient P, F)}\\
\end{exports}
#endif

RationalPlaceQ(F:SumitField, P:UnivariatePolynomialCategory F, a:F):
	DifferentialPlace(Quotient P, F) == add {
		macro Q == Quotient P;

		local center:P				== monom - a::P;
		local centerq:Q				== center::Q;
		local nu:P -> Integer			== order center;
		local nuquo:P -> (Integer, P)		== orderquo center;
		orderDrop(D:Derivation Q):Integer == prev orderOf D centerq;
		value(p:Q):F		== numerator(p)(a) / denominator(p)(a);
		orderOf(p:Q):Integer	== nu(numerator p) - nu(denominator p);

		normal?(D:Derivation Q):Boolean	== {
			import from Integer;
			zero? orderOf D centerq;
		}


		leadingCoefficient(p:Q):F == {
			zero? p => 0;
			(n, c) := nuquo numerator p;
			(m, d) := nuquo denominator p;
			c(a) / d(a);
		}

		orderOf(p:Q, m:Integer):Partial Integer == {
			zero? p or (n := orderOf p) > m => failed;
			[n];
		}

		residue(D:Derivation Q):F == {
			leadingCoefficient(D(centerq) / centerq);
		}
}

#if SUMITTEST
---------------------- test ratplace.as --------------------------
#include "sumittest"

macro {
	Z  == Integer;
	Q  == Quotient Z;
	Qx == DenseUnivariatePolynomial(Q, "x");
	X0 == RationalPlace(Q, Qx, 0);
}

x0():Boolean == {
	import from Z, Q, Qx, X0;

	x := monomial(1, 1);
	a := x^3; b := x^2 + x; c := -(1@Qx);
	na := orderOf a; nb := orderOf b; nc := orderOf c;
	D := derivation()$Qx;
	ok? := normal? D; mu := orderDrop D; r := residue D;
	na = 3 and nb = 1 and zero? nc and ok? and mu = -1 and r = 1;
}

print << "Testing ratplace..." << newline;
sumitTest("x = 0", x0);
print << newline;
#endif
