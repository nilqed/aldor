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
----------------------------- sit_skpolc.as --------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "sumit"

macro Z	== Integer;

#if ALDOC
\thistype{UnivariateSkewPolynomialCategory}
\History{Manuel Bronstein}{4/11/94}{created}
\Usage{\this~R: Category}
\Params{ {\em R} & \astype{Ring} & The coefficient ring\\ }
\Descr{\this~is the category of univariate skew polynomials with coefficients
in R.}
\begin{exports}
\category{\astype{UnivariatePolynomialAlgebra} R}\\
\asexp{apply}: & (\%, R, R) $\to$ R & Apply a skew--polynomial to a scalar\\
\end{exports}
\begin{exports}[if R has \astype{Field} then]
\asexp{leftDivide}: & (\%, \%) $\to$ (\%, \%) & Left Euclidean division\\
\asexp{leftExtendedGcd}:
& (\%, \%) $\to$ (\%, \%, \%) & Left extended Euclidean algorithm\\
\asexp{leftGcd}: & (\%, \%) $\to$ \% & Greatest common left divisor\\
\asexp{leftLcm}: & (\%, \%) $\to$ \% & Least common left multiple\\
\asexp{leftQuotient}: & (\%, \%) $\to$ \% & Left Euclidean quotient\\
\asexp{leftRemainder}: & (\%, \%) $\to$ \% & Left Euclidean remainder\\
\asexp{rightDivide}: & (\%, \%) $\to$ (\%, \%) & Right Euclidean division\\
\asexp{rightExtendedGcd}:
& (\%, \%) $\to$ (\%, \%, \%) & Right extended Euclidean algorithm\\
\asexp{rightGcd}: & (\%, \%) $\to$ \% & Greatest common right divisor\\
\asexp{rightLcm}: & (\%, \%) $\to$ \% & Least common right multiple\\
\asexp{rightQuotient}: & (\%, \%) $\to$ \% & Right Euclidean quotient\\
\asexp{rightRemainder}: & (\%, \%) $\to$ \% & Right Euclidean remainder\\
\asexp{sparseLeftMultiple}:
& (\%, \astype{Integer}) $\to$ \% & Left-Multiple in $k[x^n]$\\
\end{exports}
\begin{exports}[if R has \astype{IntegralDomain} then]
\category{\astype{NonCommutativeIntegralDomain}}\\
\asexp{monicLeftDivide}: & (\%, \%) $\to$ (\%, \%) & Left Euclidean division\\
\asexp{monicRightDivide}: & (\%, \%) $\to$ (\%, \%) & Right Euclidean division\\
\asexp{monicSparseLeftMultiple}:
& (\%, \astype{Integer}) $\to$ \% & Left-Multiple in $k[x^n]$\\
\end{exports}
#endif

UnivariateSkewPolynomialCategory(R:Ring): Category ==
	UnivariatePolynomialAlgebra R with {
	if R has IntegralDomain then NonCommutativeIntegralDomain;
	apply: (%, R, R) -> R;
#if ALDOC
\aspage{apply}
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
#endif
	if R has Field then {
		leftDivide: (%, %) -> (%, %);
		leftQuotient: (%, %) -> %;
		leftRemainder: (%, %) -> %;
#if ALDOC
\aspage{leftDivide,leftQuotient,leftRemainder}
\astarget{leftDivide}
\astarget{leftQuotient}
\astarget{leftRemainder}
\Usage{leftDivide(a, b)\\ leftQuotient(a, b)\\ leftRemainder(a, b)}
\Signatures{
leftDivide: & (\%,\%) $\to$ (\%, \%)\\
leftQuotient,leftRemainder: & (\%,\%) $\to$ \%\\
}
\Params{
{\em a } & \% & A skew--polynomial\\
{\em b } & \% & A nonzero skew--polynomial\\
}
\Retval{leftRemainder(a, b) returns $r$ such that $a = b q + r$ and
either $r = 0$ or $\deg(r) < \deg(b)$,
leftQuotient(a, b) returns $q$ such that $a - b q = 0$
or $\deg(a - b q) < \deg(b)$, and leftDivide(a, b) returns
the pair (leftQuotient(a, b), leftRemainder(a, b)).}
\seealso{\asexp{monicLeftDivide}, \asexp{rightDivide}}
#endif
		leftExtendedGcd: (%, %) -> (%, %, %);
#if ALDOC
\aspage{leftExtendedGcd}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{(\%, \%, \%)}
\Params{ {\em a,b } & \% & Skew--polynomials\\ }
\Retval{Returns $(g, c, d)$ such that $g = a c + b d$
is a left gcd of $a$ and $b$.}
\seealso{\asexp{leftGcd},\asexp{leftLcm},\asexp{rightExtendedGcd}}
#endif
		leftGcd: (%, %) -> %;
#if ALDOC
\aspage{leftGcd}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{\%}
\Params{ {\em a,b } & \% & Skew--polynomials\\ }
\Retval{Returns $g$ such that $a = g s$, $b = g t$, and every other
exact left divisor of $a$ and $b$ is a left divisor of $g$.}
\seealso{\asexp{leftExtendedGcd},\asexp{leftLcm},\asexp{rightGcd}}
#endif
		leftLcm: (%, %) -> %;
#if ALDOC
\aspage{leftLcm}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{\%}
\Params{ {\em a,b } & \% & Skew--polynomials\\ }
\Retval{Returns $l$ such that $l = s a = t b$, and every other
left multiple of $a$ and $b$ is a left multiple of $l$.}
\seealso{\asexp{leftExtendedGcd},\asexp{leftGcd},\asexp{rightLcm}}
#endif
	}
	if R has IntegralDomain then {
		monicLeftDivide: (%, %) -> (%, %);
#if ALDOC
\aspage{monicLeftDivide}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{(\%, \%)}
\Params{
{\em a } & \% & The skew--polynomial to be divided\\
{\em b } & \% & The skew--polynomial to divide by (must be monic)\\
}
\Retval{Returns $(q, r)$ such that $a = b q + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{\asexp{leftDivide}, \asexp{monicRightDivide}}
#endif
		monicRightDivide: (%, %) -> (%, %);
#if ALDOC
\aspage{monicRightDivide}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{(\%, \%)}
\Params{
{\em a } & \% & The skew--polynomial to be divided\\
{\em b } & \% & The skew--polynomial to divide by (must be monic)\\
}
\Retval{Returns $(q, r)$ such that $a = q b + r$ and either $r = 0$
or $\deg(r) < \deg(b)$.}
\seealso{\asexp{monicLeftDivide},\asexp{rightDivide}}
#endif
		monicSparseLeftMultiple: (%, Z) -> %;
	}
	if R has Field then {
		sparseLeftMultiple: (%, Z) -> %;
#if ALDOC
\aspage{monicSparseLeftMultiple,sparseLeftMultiple}
\astarget{monicSparseLeftMultiple}
\astarget{sparseLeftMultiple}
\Usage{monicSparseLeftMultiple(p, n)\\ sparseLeftMultiple(p,n)}
\Signature{(\%, \astype{Integer})}{\%}
\Params{
{\em p} & \% & A skew--polynomial\\
{\em n} & \astype{Integer} & A positive integer\\
}
\Retval{Returns a nonzero $q = \sum_{i=0}^m a_i x^i$
of minimal degree such that $q(x^n) = a p$ for some skew--polynomial $a$.}
\Remarks{$p$ must be monic in a call to monicSparseLeftMultiple. The
function sparseLeftMultiple is only provided when $R$ has \astype{Field}.}
#endif
		rightDivide: (%, %) -> (%, %);
		rightQuotient: (%, %) -> %;
		rightRemainder: (%, %) -> %;
#if ALDOC
\aspage{rightDivide,rightQuotient,rightRemainder}
\astarget{rightDivide}
\astarget{rightQuotient}
\astarget{rightRemainder}
\Usage{rightDivide(a, b)\\ rightQuotient(a, b)\\ rightRemainder(a, b)}
\Signatures{
rightDivide: & (\%,\%) $\to$ (\%, \%)\\
rightQuotient,rightRemainder: & (\%,\%) $\to$ \%\\
}
\Params{
{\em a } & \% & A skew--polynomial\\
{\em b } & \% & A nonzero skew--polynomial\\
}
\Retval{rightRemainder(a, b) returns $r$ such that $a = q b + r$ and
either $r = 0$ or $\deg(r) < \deg(b)$,
rightQuotient(a, b) returns $q$ such that $a - q b = 0$
or $\deg(a - q b) < \deg(b)$, and rightDivide(a, b) returns
the pair (rightQuotient(a, b), rightRemainder(a, b)).}
\seealso{\asexp{leftDivide},\asexp{monicRightDivide}}
#endif
		rightExtendedGcd: (%, %) -> (%, %, %);
#if ALDOC
\aspage{rightExtendedGcd}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{(\%, \%, \%)}
\Params{ {\em a,b } & \% & Skew--polynomials\\ }
\Retval{Returns $(g, c, d)$ such that $g = c a + d b$
is a right gcd of $a$ and $b$.}
\seealso{\asexp{leftExtendedGcd},\asexp{rightGcd},\asexp{rightLcm}}
#endif
		rightGcd: (%, %) -> %;
#if ALDOC
\aspage{rightGcd}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{\%}
\Params{ {\em a,b } & \% & Skew--polynomials\\ }
\Retval{Returns $g$ such that $a = s g$, $b = t g$, and every other
exact right divisor of $a$ and $b$ is a right divisor of $g$.}
\seealso{\asexp{leftGcd},\asexp{rightExtendedGcd},\asexp{rightLcm}}
#endif
		rightLcm: (%, %) -> %;
#if ALDOC
\aspage{rightLcm}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{\%}
\Params{ {\em a,b } & \% & Skew--polynomials\\ }
\Retval{Returns $l$ such that $l = a s = b t$, and every other
right multiple of $a$ and $b$ is a right multiple of $l$.}
\seealso{\asexp{leftLcm},\asexp{rightExtendedGcd},\asexp{rightGcd}}
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

		if R has IntegralDomain then {
			monicSparseLeftMultiple(a:%, N:Z):% == {
				import from MachineInteger;
				macro RC == (R pretend CommutativeRing);
				import from LinearAlgebra(RC, DenseMatrix R);
				assert(N > 0);
				zero? a or zero?(d := degree a) or one? N => a;
				m := machine d;
				firstDependence(remgen(N, a, m), m)::%;
			}

			-- generates x^{in} mod p for i = 0,1,...
			local remgen(n:Z, p:%, dim:MachineInteger):_
			Generator Vector R == generate {
				import from R;
				assert(n > 1);
				v:Vector R := zero dim;
				vec! := vectorize! v;
				y:% := 1;
				yield vec! y;
				xn := monomial(1, n);
				repeat {
					(q, y) := monicRightDivide(xn * y, p);
					yield vec! y;
				}
			}
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

			sparseLeftMultiple(a:%, n:Z):% ==
				monicSparseLeftMultiple(a, n);

			leftExtendedGcd(a:%, b:%):(%, %, %) ==
				extended(a, b, leftEEA);

			rightExtendedGcd(a:%, b:%):(%, %, %) ==
				extended(a, b, rightEEA);

			local exactQuot(q:%, r:%):Partial % == {
				zero? r => [q];
				failed;
			}

			leftExactQuotient(a:%, b:%):Partial % ==
				exactQuot leftDivide(a, b);

			rightExactQuotient(a:%,b:%):Partial % ==
				exactQuot rightDivide(a,b);

			-- returns (g = leftGcd(a, b), c, d, l = rightLcm(a, b))
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

			-- returns (g, c, d) such that g = c1 a + c2 b
			local extended(a:%,b:%,eea:(%,%)->(%,%,%,%)):(%,%,%)=={
				import from Z;
				zero? a => (b, 0, 1);
				zero? b => (a, 1, 0);
				degree a < degree b => {
					(g, c1, c2, l) := eea(b, a);
					(g, c2, c1);
				}
				(g, c1, c2, l) := eea(a, b);
				(g, c1, c2)
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
