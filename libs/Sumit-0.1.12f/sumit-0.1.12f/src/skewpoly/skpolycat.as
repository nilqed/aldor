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
----------------------------- skpolycat.as --------------------------------
#include "sumit"

#if ASDOC
\thistype{UnivariateSkewPolynomialCategory}
\History{Manuel Bronstein}{4/11/94}{created}
\Usage{\this~R: Category}
\Params{
{\em R} & CommutativeRing & The coefficient ring of the skew polynomials\\
}
\Descr{\this~is the category of univariate skew polynomials with coefficients
in an arbitrary field R.}
\begin{exports}
\category{UnivariateFreeAlgebraCategory R}\\
apply: & (\%, R, R) $\to$ R & Apply a skew-polynomial to a scalar\\
\end{exports}
\begin{exports}[if R has IntegralDomain then]
\category{NonCommutativeIntegralDomain}\\
monicLeftDivide: & (\%, \%) $\to$ (\%, \%) & Left Euclidean division\\
monicRightDivide: & (\%, \%) $\to$ (\%, \%) & Right Euclidean division\\
\end{exports}
\begin{exports}[if R has Field then]
leftDivide: & (\%, \%) $\to$ (\%, \%) & Left Euclidean division\\
leftExtendedGcd: & (\%, \%) $\to$ EXT & Left extended Euclidean algorithm\\
leftGcd: & (\%, \%) $\to$ \% & Greatest common left divisor\\
leftLcm: & (\%, \%) $\to$ \% & Least common left multiple\\
leftQuotient: & (\%, \%) $\to$ \% & Left Euclidean quotient\\
leftRemainder: & (\%, \%) $\to$ \% & Left Euclidean remainder\\
rightDivide: & (\%, \%) $\to$ (\%, \%) & Right Euclidean division\\
rightExtendedGcd: & (\%, \%) $\to$ EXT & Right extended Euclidean algorithm\\
rightGcd: & (\%, \%) $\to$ \% & Greatest common right divisor\\
rightLcm: & (\%, \%) $\to$ \% & Least common right multiple\\
rightQuotient: & (\%, \%) $\to$ \% & Right Euclidean quotient\\
rightRemainder: & (\%, \%) $\to$ \% & Right Euclidean remainder\\
\end{exports}
\Aswhere{
EXT &==& Record(coef1:\%, coef2:\%, generator:\%)\\
}
#endif

macro {
	Z	== Integer;
	EEA	== Record(coef1:%, coef2:%, generator:%);
}

UnivariateSkewPolynomialCategory(R:CommutativeRing): Category ==
	UnivariateFreeAlgebraCategory R with {
	if R has IntegralDomain then NonCommutativeIntegralDomain;
	apply: (%, R, R) -> R;
#if ASDOC
\begin{aspage}{apply}
\Usage{ \name(p, c, a)\\ p(c, a) }
\Signature{(\%, R, R)}{R}
\Params{
{\em p} & \% & A skew polynomial\\
{\em c} & R  & An element of the ring\\
{\em a} & R  & The element to apply $p$ to\\
}
\Retval{Returns
$$
\sum_{i=0}^n a_i\, (c \sigma + \delta)^i\, (a)
$$
where $p = \sum_{i=0}^n a_i x^i$ and $\sigma, \delta$ determine the
skew-polynomial ring.}
\end{aspage}
#endif
	if R has Field then {
		leftDivide: (%, %) -> (%, %);
#if ASDOC
\begin{aspage}{leftDivide}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{(\%, \%)}
\Params{
{\em a } & \% & The polynomial to be divided\\
{\em b } & \% & The polynomial to divide by\\
}
\Retval{Returns $(q, r)$ such that $a = b q + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{leftQuotient(\this),\\ leftRemainder(\this),\\
monicLeftDivide(\this),\\ rightDivide(\this)}
\end{aspage}
#endif
		leftExtendedGcd: (%, %) -> EEA;
#if ASDOC
\begin{aspage}{leftExtendedGcd}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{Record(coef1:\%, coef2:\%, generator:\%)}
\Params{
{\em a } & \% & A polynomial\\
{\em b } & \% & A polynomial\\
}
\Retval{Returns $[c, d, g]$ such that $g = a c + b d$
is a left gcd of $a$ and $b$.}
\seealso{leftGcd(\this),\\ leftLcm(\this),\\ rightExtendedGcd(\this)}
\end{aspage}
#endif
		leftGcd: (%, %) -> %;
#if ASDOC
\begin{aspage}{leftGcd}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{\%}
\Params{
{\em a } & \% & A polynomial\\
{\em b } & \% & A polynomial\\
}
\Retval{Returns $g$ such that $a = g s$, $b = g t$, and every other
exact left divisor of $a$ and $b$ is a left divisor of $g$.}
\seealso{leftExtendedGcd(\this),\\ leftLcm(\this),\\ rightGcd(\this)}
\end{aspage}
#endif
		leftLcm: (%, %) -> %;
#if ASDOC
\begin{aspage}{leftLcm}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{\%}
\Params{
{\em a } & \% & A polynomial\\
{\em b } & \% & A polynomial\\
}
\Retval{Returns $l$ such that $l = s a = t b$, and every other
left multiple of $a$ and $b$ is a left multiple of $l$.}
\seealso{leftExtendedGcd(\this),\\ leftGcd(\this),\\ rightLcm(\this)}
\end{aspage}
#endif
		leftQuotient: (%, %) -> %;
#if ASDOC
\begin{aspage}{leftQuotient}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{\%}
\Params{
{\em a } & \% & The polynomial to be divided\\
{\em b } & \% & The polynomial to divide by\\
}
\Retval{Returns $q$ such that $a = b q + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{leftDivide(\this),\\ leftRemainder(\this),\\
monicLeftDivide(\this),\\ rightQuotient(\this)}
\end{aspage}
#endif
		leftRemainder: (%, %) -> %;
#if ASDOC
\begin{aspage}{leftRemainder}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{(\%, \%)}
\Params{
{\em a } & \% & The polynomial to be divided\\
{\em b } & \% & The polynomial to divide by\\
}
\Retval{Returns $r$ such that $a = b q + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{leftDivide(\this),\\ leftQuotient(\this),\\
monicLeftDivide(\this),\\ rightRemainder(\this)}
\end{aspage}
#endif
	}
	if R has IntegralDomain then {
		monicLeftDivide: (%, %) -> (%, %);
#if ASDOC
\begin{aspage}{monicLeftDivide}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{(\%, \%)}
\Params{
{\em a } & \% & The polynomial to be divided\\
{\em b } & \% & The polynomial to divide by (must be monic)\\
}
\Retval{Returns $(q, r)$ such that $a = b q + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{leftDivide(\this),\\ leftQuotient(\this),\\
leftRemainder(\this),\\ monicRightDivide(\this)}
\end{aspage}
#endif
		monicRightDivide: (%, %) -> (%, %);
#if ASDOC
\begin{aspage}{monicRightDivide}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{(\%, \%)}
\Params{
{\em a } & \% & The polynomial to be divided\\
{\em b } & \% & The polynomial to divide by (must be monic)\\
}
\Retval{Returns $(q, r)$ such that $a = q b + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{monicLeftDivide(\this),\\ rightDivide(\this),\\
rightQuotient(\this),\\ rightRemainder(\this)}
\end{aspage}
#endif
	}
	if R has Field then {
		rightDivide: (%, %) -> (%, %);
#if ASDOC
\begin{aspage}{rightDivide}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{(\%, \%)}
\Params{
{\em a } & \% & The polynomial to be divided\\
{\em b } & \% & The polynomial to divide by\\
}
\Retval{Returns $(q, r)$ such that $a = q b + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{leftDivide(\this),\\ monicRightDivide(\this),\\
rightQuotient(\this),\\ rightRemainder(\this)}
\end{aspage}
#endif
		rightExtendedGcd: (%, %) -> EEA;
#if ASDOC
\begin{aspage}{rightExtendedGcd}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{Record(coef1:\%, coef2:\%, generator:\%)}
\Params{
{\em a } & \% & A polynomial\\
{\em b } & \% & A polynomial\\
}
\Retval{Returns $[c, d, g]$ such that $g = c a + d b$
is a right gcd of $a$ and $b$.}
\seealso{leftExtendedGcd(\this),\\ rightGcd(\this),\\ rightLcm(\this)}
\end{aspage}
#endif
		rightGcd: (%, %) -> %;
#if ASDOC
\begin{aspage}{rightGcd}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{\%}
\Params{
{\em a } & \% & A polynomial\\
{\em b } & \% & A polynomial\\
}
\Retval{Returns $g$ such that $a = s g$, $b = t g$, and every other
exact right divisor of $a$ and $b$ is a right divisor of $g$.}
\seealso{leftGcd(\this),\\ rightExtendedGcd(\this),\\ rightLcm(\this)}
\end{aspage}
#endif
		rightLcm: (%, %) -> %;
#if ASDOC
\begin{aspage}{rightLcm}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{\%}
\Params{
{\em a } & \% & A polynomial\\
{\em b } & \% & A polynomial\\
}
\Retval{Returns $l$ such that $l = a s = b t$, and every other
right multiple of $a$ and $b$ is a right multiple of $l$.}
\seealso{leftLcm(\this),\\ rightExtendedGcd(\this),\\ rightGcd(\this)}
\end{aspage}
#endif
		rightQuotient: (%, %) -> %;
#if ASDOC
\begin{aspage}{rightQuotient}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{(\%, \%)}
\Params{
{\em a } & \% & The polynomial to be divided\\
{\em b } & \% & The polynomial to divide by\\
}
\Retval{Returns $q$ such that $a = q b + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{leftDivide(\this),\\ monicRightDivide(\this),\\
rightDivide(\this),\\ rightRemainder(\this)}
\end{aspage}
#endif
		rightRemainder: (%, %) -> %;
#if ASDOC
\begin{aspage}{rightRemainder}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{(\%, \%)}
\Params{
{\em a } & \% & The polynomial to be divided\\
{\em b } & \% & The polynomial to divide by\\
}
\Retval{Returns $r$ such that $a = q b + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{leftRemainder(\this),\\ monicRightDivide(\this),\\
rightDivide(\this),\\ rightQuotient(\this)}
\end{aspage}
#endif
	}
	default {
		(a:R) * (y:%):% == {
			z:% := 0;
			for term in y repeat {
				(c, n) := term;
				z := add!(z, a * c, n);
			}
			z;
		}

		if R has Field then {
			rightLcm(a:%, b:%):%	== nclcm(a, b, leftEEA);
			leftLcm(a:%, b:%):%	== nclcm(a, b, rightEEA);
			rightGcd(a:%, b:%):%	== ncgcd(a, b, rightRemainder);
			leftGcd(a:%, b:%):%	== ncgcd(a, b, leftRemainder);
			leftQuotient(a:%, b:%):%== {(q,r):= leftDivide(a,b); q }
			leftRemainder(a:%, b:%):%== {(q,r):= leftDivide(a,b); r}
			rightQuotient(a:%, b:%):%== {(q,r):= rightDivide(a,b);q}
			rightRemainder(a:%, b:%):%== {(q,r):=rightDivide(a,b);r}
			leftExtendedGcd(a:%,b:%):EEA == extended(a, b, leftEEA);
			rightExtendedGcd(a:%,b:%):EEA == extended(a,b,rightEEA);

			local exactQuot(q:%, r:%):Partial % == {
				zero? r => [q];
				failed;
			}

			leftExactQuotient(a:%, b:%):Partial % ==
				exactQuot leftDivide(a, b);

			rightExactQuotient(a:%,b:%):Partial % ==
				exactQuot rightDivide(a,b);

			-- returns [g = leftGcd(a, b), c, d, l = rightLcm(a, b)]
			-- such that g := a c + b d
			local leftEEA(a:%, b:%):(%, %, %, %) == {
				a0 := a;
				u0:% := v:% := 1;
				v0:% := u:% := 0;
				while b ~= 0 repeat {
					(q, r) := leftDivide(a, b);
					(a, b) := (b, r);
					(u0, u):= (u, u0 - u * q);
					(v0, v):= (v, v0 - v * q)
				}
				(a, u0, v0, a0 * u)
			}

			local ncgcd(a:%, b:%, ncrem:(%, %) -> %):% == {
				import from Z;
				zero? a => b;
				zero? b => a;
				degree a < degree b => ncgcd(b, a, ncrem);
				while b ~= 0 repeat (a, b) := (b, ncrem(a, b));
				a
			}

			local extended(a:%, b:%, eea:(%,%)->(%,%,%,%)):EEA == {
				import from Z;
				zero? a => [0, 1, b];
				zero? b => [1, 0, a];
				degree a < degree b => {
					(g, c1, c2, l) := eea(b,a);
					[c2, c1, g];
				}
				(g, c1, c2, l) := eea(a, b);
				[c1, c2, g]
			}

			local nclcm(a:%, b:%, eea:(%,%) -> (%,%,%,%)):% == {
				import from Z;
				zero? a or zero? b => 0;
				degree a < degree b => nclcm(b, a, eea);
				(g, c1, c2, l) := eea(b, a);
				l
			}

			-- returns [g = rightGcd(a, b), c, d, l = leftLcm(a, b)]
			-- such that g := c a + d b
			local rightEEA(a:%, b:%):(%, %, %, %) == {
				a0 := a;
				u0:% := v:% := 1;
				v0:% := u:% := 0;
				while b ~= 0 repeat {
					(q, r) := rightDivide(a, b);
					(a, b) := (b, r);
					(u0, u):= (u, u0 - q * u);
					(v0, v):= (v, v0 - q * v)
				}
				(a, u0, v0, u * a0)
			}
		}
	}   -- end from default definitions
}
