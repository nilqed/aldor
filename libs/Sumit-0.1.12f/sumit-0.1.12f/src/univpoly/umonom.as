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
----------------------------- umonom.as ----------------------------------
#include "sumit.as"

#if ASDOC
\thistype{UnivariateMonomial}
\History{Manuel Bronstein}{20/5/94}{created}
\Usage{import from \this~R}
\Params{ {\em R} & SumitRing & The coefficient ring of the polynomials\\ }
\Descr{\this~R implements univariate monomials with coefficients in R.}
\begin{exports}
\category{Order}\\
apply: & (R $\to$ R, \%) $\to$ \% & Applies a function to the coefficient\\
coefficient: & \% $\to$ R & Extraction of the coefficient\\
degree: & \% $\to$ Integer & The degree of a monomial\\
monomial: & (R, Z) $\to$ \% & Creation of a monomial\\
setCoefficient!: & (\%, R) $\to$ R & In-place coefficient modification\\
setDegree!: & (\%, Z) $\to$ Z & In-place degree modification\\
\end{exports}
#endif

macro Z == Integer;

UnivariateMonomial(R:SumitRing): Order with {
	apply: (R -> R, %) -> %;
#if ASDOC
\aspage{apply}
\Usage{ \name(f, p)\\f~p }
\Signature{(R $\to$ R}{\%}
\Params{
{\em f} & R $\to$ R & A function to apply\\
{\em p} & \% & A monomial\\
}
\Retval{Returns $f(a) x^n$ where $p = a x^n$, $p$ remains unchanged.}
\begin{asex}
\begin{ttyout}
import from Integer, UnivariateMonomial Integer;

print << apply((n:Integer):Integer +-> n + n, monomial(-2, 3));
\end{ttyout}
writes
\Asoutput{ \> monomial(-4, 3) }
to the standard stream print.
\end{asex}
#endif
	coefficient: % -> R;
#if ASDOC
\aspage{coefficient}
\Usage{\name~p}
\Signature{\this~R}{R}
\Params{ {\em p} & \this~R & A monomial\\ }
\Retval{Returns the coefficient of $p$, \ie $c$ where $p = c\; x^n$.}
\seealso{degree(\this), setCoefficient!(\this)}
#endif
	degree: % -> Z;
#if ASDOC
\aspage{degree}
\Usage{\name~p}
\Signature{\this~R}{Integer}
\Params{ {\em p} & \this~R & A monomial\\ }
\Retval{Returns the degree of $p$, \ie $n$ where $p = c\; x^n$.}
\seealso{coefficient(\this)}
#endif
	monomial: (R, Z) -> %;
#if ASDOC
\aspage{monomial}
\Usage{\name(c, n)}
\Signature{(R, Integer)}{\this~R}
\Params{
{\em c} & R & A scalar\\
{\em n} & Integer & An exponent\\
}
\Retval{Returns the monomial $c\; x^n$.}
#endif
	if R has FiniteCharacteristic then {
        	pthPower: % -> %;
        	pthPower!: % -> %;
#if ASDOC
\aspage{pthPower}
\Usage{ \name~p\\ \name!~p }
\Signatures{
\name: & \this~R $\to$ \this~R\\
\name!: & \this~R $\to$ \this~R\\
}
\Params{ {\em p} & \this~R & A monomial\\ }
\Retval{Returns $p^{\mbox{characteristic}}$.}
\Remarks{\name! reuses the storage use by p whose previous value
is lost after the call. This may cause $p$ to be destroyed,
so do not use it unless $p$ has been locally allocated,
and is guaranteed not to share space with other elements.
Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
#endif
	}
	setCoefficient!: (%, R) -> R;
#if ASDOC
\aspage{setCoefficient!}
\Usage{\name(p, c)}
\Signature{(\this~R, R)}{R}
\Params{
{\em p} & \this~R & A monomial\\
{\em c} & R & A scalar\\
}
\Descr{Sets the coefficient of $p$ to $c$,\ie changes $p = d\; x^n$ into
$c\; x^n$}
\Retval{Returns the new coefficient $c$.}
\seealso{coefficient(\this)}
#endif
	setDegree!: (%, Z) -> Z;
#if ASDOC
\aspage{setDegree!}
\Usage{\name(p, c)}
\Signature{(\this~R, Integer)}{Integer}
\Params{
{\em p} & \this~R & A monomial\\
{\em n} & Integer & An exponent\\
}
\Descr{Sets the degree of $p$ to $n$,\ie changes $p = c\; x^m$ into
$c\; x^n$}
\Retval{Returns the new degree $n$.}
\seealso{degree(\this)}
#endif
} == add {
	macro Rep == Record(coef:R, expt:Z);
	import from Rep;

	monomial(c:R, n:Z):%			== { ASSERT(n>=0); per [c, n]; }
	coefficient(t:%):R     			== rep(t).coef;
	degree(t:%):Z    	  		== rep(t).expt;
	sample:%      				== monomial(1, 1);
	setDegree!(t:%, n:Z):Z			== rep(t).expt := n;
	setCoefficient!(t:%, c:R):R		== rep(t).coef := c;
	(u:%) > (v:%):Boolean			== degree u > degree v;
	apply(f:R -> R, p:%):%		== monomial(f coefficient p, degree p);

	(u:%) = (v:%):Boolean == {
		degree u = degree v and coefficient u = coefficient v;
	}

	(p:TextWriter) << (t:%):TextWriter == {
		p << "monomial(" << coefficient t << ", " << degree t << ")";
	}

	if R has FiniteCharacteristic then {
		pthPower(p:%):% ==
			monomial(pthPower(coefficient p)$R,
					characteristic$R * degree p);

		pthPower!(p:%):% == {
			rec := rep p;
			rec.coef := pthPower(rec.coef)$R;
			rec.expt := characteristic$R * rec.expt;
			p;
		}
	}
}

#if SUMITTEST
---------------------- test umonom.as --------------------------
#include "sumittest.as"

macro {
        Z == Integer;
	F == SmallPrimeField 11;
        M == UnivariateMonomial;
}

double(a:Z):Z == a + a;

degree():Boolean == {
        import from Z, M Z;
        p := monomial(2, 3);
	q := apply(double, p);
        degree p = 3 and coefficient p = 2 and
		degree q = degree p and coefficient q = 4;
}

pthpower():Boolean == {
        import from SingleInteger, Z, F, M F;

        p := monomial(2, 3);
	q := pthPower p;
	degree p = 3 and coefficient p = 2 and
		degree q = characteristic$F * degree p
			and coefficient q = coefficient p;
}

print << "Testing umonom..." << newline;
sumitTest("degree", degree);
sumitTest("pthpower", pthpower);
print << newline;
#endif

