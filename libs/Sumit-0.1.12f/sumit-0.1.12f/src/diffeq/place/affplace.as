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
------------------------------ affplace.as --------------------
#include "sumit"

#if ASDOC
\thistype{AffinePlace}
\History{Manuel Bronstein}{26/6/95}{created}
\Usage{import from \this(R, Rx, p)}
\Params{
{\em R} & IntegralDomain & The coefficient ring of the polynomials\\
{\em Rx} & UnivariatePolynomialCategory R & A polynomial type over R\\
{\em p} & Rx & The localization center\\
}
\Descr{\this(R, Rx, p) provides the localisations of the elements of
Rx at the roots of $p(x) = 0$. The leading coefficient of $p$ must be
a unit in $R$.}
\begin{exports}
\category{DifferentialPlace(Rx, UnivariatePolynomialMod(R, Rx, p))}\\
\end{exports}
#endif

macro {
	Z == Integer;
	RR == RationalRoot;
	POLY == UnivariatePolynomialCategory;
	E == UnivariatePolynomialMod(R, Rx, center);
}

-- the leading coefficient of center must be a unit in R
AffinePlace(R:IntegralDomain, Rx:UnivariatePolynomialCategory R, center:Rx):
	DifferentialPlace(Rx, E) == add {
		local gcd?:Boolean			== R has GcdDomain;
		local nu:Rx -> Integer			== order center;
		local nuquo: Rx -> (Integer, Rx)	== orderquo center;
		orderOf(p:Rx):Integer			== nu p;
		value(p:Rx):E				== reduce p;
		orderDrop(D:Derivation Rx):Integer	== prev nu D center;
		degree:Integer				== degree center;
		residue(D:Derivation Rx):E == leadingCoefficient(D center)$%;

		normal?(D:Derivation Rx):Boolean == {
			import from R;
			gcd? => gcdnormal? D;
			~zero?(resultant(D center, center));
		}

		if R has GcdDomain then {
			local gcddeg(a:Rx, b:Rx):Z == degree gcd(a, b);

			local gcdnormal?(D:Derivation Rx):Boolean == {
				import from Integer;
				zero? degree gcd(D center, center);
			}
		}

		leadingCoefficient(p:Rx):E == {
			zero? p => 0;
			(n, p) := nuquo p;
			value p;
		}

		orderOf(p:Rx, m:Integer):Partial Integer == {
			zero? p or (n := orderOf p) > m => failed;
			[n];
		}

		multiplicity(r:RR, P:POLY E):P -> Z == {
			import from E;
			(n, d) := value r;
			m := multiplicity r;
			val := value P;
			(p:P):Z +-> {
				v := val(p, n, d);
				zero? v => degree$%;
				gcd? => gcddeg(lift v, center);
				m;
			}
		}
}

#if ASDOC
\thistype{AffinePlace1}
\History{Manuel Bronstein}{13/12/96}{created}
\Usage{import from \this(R, Rx, p, Q, Qx, q)}
\Params{
{\em R} & IntegralDomain & The coefficient ring of the polynomials\\
{\em Rx} & UnivariatePolynomialCategory R & A polynomial type over R\\
{\em p} & Rx & The localization center\\
{\em Q} & QuotientCategory R & A localization of R\\
{\em Qx} & UnivariatePolynomialCategory Q & A polynomial type over Q\\
{\em q} & Qx & $p$ seen as a polynomial over Q\\
}
\Descr{\this(R, Rx, p, Q, Qx, q) provides the localisations of the elements of
Rx at the roots of $p(x) = 0$, also when the leading coefficient $p$
is not a unit in $R$, as long as it is a unit in $Q$. $q$ must be a multiple
of $p$, but with coefficients in $p$. In addition, $p$ must be primitive
if $R$ is a Gcd domain. For efficiency, use {\tt AffinePlace} whenever
the leading coefficient of $p$ is already a unit in $R$.}
\begin{exports}
\category{DifferentialPlace(Rx, UnivariatePolynomialMod(Q, Qx, q))}\\
\end{exports}
#endif

macro F == UnivariatePolynomialMod(Q, Qx, qcenter);

-- center should be primitive if R is a Gcd domain
AffinePlace1(R:IntegralDomain, Rx:UnivariatePolynomialCategory R, center:Rx,
		Q:QuotientCategory R, Qx:UnivariatePolynomialCategory Q,
		qcenter:Qx): DifferentialPlace(Rx, F) == add {
		local gcd?:Boolean			== R has GcdDomain;
		local nu:Rx -> Integer			== order center;
		local nuquo: Rx -> (Integer, Rx)	== orderquo center;
		value(p:Rx):F				== reduce localize p;
		orderOf(p:Rx):Integer			== nu p;
		orderDrop(D:Derivation Rx):Integer	== prev nu D center;
		degree:Integer				== degree center;
		residue(D:Derivation Rx):F == leadingCoefficient(D center)$%;

		local localize(p:Rx):Qx == {
			import from Q;
			q:Qx := 0;
			for term in p repeat {
				(c, n) := term;
				q := add!(q, c::Q, n);
			}
			q;
		}

		normal?(D:Derivation Rx):Boolean == {
			import from R;
			gcd? => gcdnormal? D;
			~zero?(resultant(D center, center));
		}

		if R has GcdDomain then {
			local gcddeg(a:Qx, b:Qx):Z == degree gcd(a, b);

			local gcdnormal?(D:Derivation Rx):Boolean == {
				import from Integer;
				zero? degree gcd(D center, center);
			}
		}

		leadingCoefficient(p:Rx):F == {
			zero? p => 0;
			(n, p) := nuquo p;
			value p;
		}

		orderOf(p:Rx, m:Integer):Partial Integer == {
			zero? p or (n := orderOf p) > m => failed;
			[n];
		}

		multiplicity(r:RR, P:POLY F):P -> Z == {
			import from F;
			(n, d) := value r;
			m := multiplicity r;
			val := value P;
			(p:P):Z +-> {
				v := val(p, n, d);
				zero? v => degree$%;
				gcd? => gcddeg(lift v, qcenter);
				m;
			}
		}
}
