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
----------------------------- sit_upolc.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "sumit"

macro {
	Z == Integer;
	UPC0 == UnivariatePolynomialCategory0 %;
	FR == FractionalRoot;
	RR == FR Z;
	RES== Resultant(R pretend IntegralDomain, %);
	GN == Generator;
	FRR==FR(R pretend CommutativeRing);
	REC == Record(sigmaexp:Z, exponent:Z);
	ORBIT == Cross(%, List REC);
}

#if ALDOC
%
% Describes also the exports of UnivariatePolynomialCategory0, which is
% not documented separately.
%
\thistype{UnivariatePolynomialCategory}
\History{Manuel Bronstein}{20/5/94}{created}
\History{Manuel Bronstein}{21/9/95}{added Zippel's multiple gcd (upolc0)}
\History{Manuel Bronstein}{20/9/95}{added check for UnivariateGcdRing}
\History{Thom Mulders}{27/5/97}{added bidirectional exact quotient (upolc0)}
\Usage{\this~R: Category}
\Params{
{\em R} & \astype{SumitType} & The coefficient domain\\
        & \astype{ArithmeticType} &\\
}
\Descr{\this~is the category of univariate polynomials with coefficients in
an arbitrary domain R and with respect to the power basis $(x^n)_{n \ge 0}$.}

\begin{exports}
\category{\astype{UnivariatePolynomialAlgebra} R}\\
\asexp{apply}: & (\%, R) $\to$ R & Evaluate a polynomial\\
\asexp{apply}: & (\%, \%) $\to$ \% & Evaluate a polynomial\\
\asexp{equal?}:
& (\%, \%, \%, \astype{Integer}) $\to$ \astype{Boolean} & Truncated equality\\
\asexp{Horner}: & (\%, R) $\to$ (\%, R) & Horner division by $x - a$\\
\end{exports}

\begin{exports}[if $R$ has \astype{CommutativeRing} then]
\category{\astype{DifferentialRing}}\\
\asexp{lift}: & (\astype{Derivation} R, \%) $\to$ \astype{Derivation} \% &
Extend a derivation\\
\end{exports}

\begin{exports}
[if $R$ has \astype{CommutativeRing} and $R$ has \astype{QRing} then]
\asexp{integrate}: & \% $\to$ \% & Integration\\
& (\%, \astype{Integer}) $\to$ \% & \\
\end{exports}

\begin{exports}[if $R$ has \astype{FactorizationRing} then]
\asexp{factor}:
& \% $\to$ (R, \astype{Product} \%) & Factorisation into irreducibles\\
\asexp{fractionalRoots}:
& \% $\to$ \astype{Generator} \astype{FractionalRoot} R &
Roots in the fraction field\\
\asexp{roots}:
& \% $\to$ \astype{Generator} \astype{FractionalRoot} R &
Roots in the coefficient ring\\
\end{exports}

\begin{exports}[if $R$ has \astype{Field} then]
\category{\astype{EuclideanDomain}}\\
\asexp{sparseMultiple}:
& (\%, \astype{Integer}) $\to$ \% & Multiple in $k[x^n]$\\
\end{exports}

\begin{exports}[if $R$ has \astype{GcdDomain} then]
\category{\astype{DecomposableRing}}\\
\category{\astype{GcdDomain}}\\
\asexp{squareFree}:
& \% $\to$ (R, \astype{Product} \%) & Squarefree factorisation\\
\asexp{squareFreePart}: & \% $\to$ \% & Squarefree part\\
\end{exports}

\begin{exports}
[if $R$ has \astype{GcdDomain} and $R$ has \astype{RationalRootRing} then]
\asexp{dispersion}: & \% $\to$ \astype{Integer} & Dispersion\\
                    & (\%, \%) $\to$ \astype{Integer} & \\
\asexp{integerDistances}:
& \% $\to$ \astype{List} \astype{Integer} & Integer spread\\
& (\%, \%) $\to$ \astype{List} \astype{Integer} & \\
\asexp{universalBound}:
& (\%,\%) $\to$ \astype{List} \builtin{Cross}(\%, \astype{Integer}) &
Universal bound\\
\end{exports}

\begin{exports}[if $R$ has \astype{IntegralDomain} then]
\category{\astype{IntegralDomain}}\\
\asexp{monicDivide}: & (\%, \%) $\to$ (\%, \%) & Polynomial division\\
\asexp{monicRemainder}: & (\%, \%) $\to$ \% & Remainder\\
\asexp{monicRemainder!}: & (\%, \%) $\to$ \% & Remainder\\
\asexp{pseudoDivide}: & (\%, \%) $\to$ (\%, \%) & Polynomial pseudo--division\\
\asexp{pseudoRemainder}: & (\%, \%) $\to$ \% & Pseudo--remainder\\
\asexp{pseudoRemainder!}: & (\%, \%) $\to$ \% & Pseudo--remainder\\
\asexp{resultant}: & (\%, \%) $\to$ R & Resultant of 2 polynomials\\
\end{exports}

\begin{exports}[if $R$ has \astype{OrderedArithmeticType} then]
\asexp{height}: & \% $\to$ R & Max norm over all the coefficients\\
\end{exports}

\begin{exports}[if $R$ has \astype{RationalRootRing} then]
\category{\astype{RationalRootRing}}\\
\asexp{integerRoots}:
& \% $\to$ \astype{Generator} \astype{FractionalRoot} \astype{Integer} &
Integer roots\\
\asexp{rationalRoots}:
& \% $\to$ \astype{Generator} \astype{FractionalRoot} \astype{Integer} &
Rational roots\\
\end{exports}

\begin{exports}[if $R$ has \astype{Ring} then]
\asexp{ordinaryPoint}:
& \% $\to$ \astype{Integer} & Point where a polynomial is nonzero\\
\asexp{values}:
& (\%, R) $\to$ \astype{Generator} R & Generate values of a polynomial\\
\end{exports}

\begin{exports}[if $R$ has \astype{Specializable} then]
\category{\astype{Specializable}}\\
\end{exports}

% This loads the aspage's for UnivariatePolynomialCategory0
\input sit_upolc0.tex
#endif

UnivariatePolynomialCategory(R:Join(SumitType, ArithmeticType)):Category ==
	UnivariatePolynomialCategory0 R with {
	if R has FactorizationRing then {
		factor: % -> (R, Product %);
#if ALDOC
\aspage{factor}
\Usage{ \name~p }
\Signature{\%}{(R, \astype{Product} \%)}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns $(c, p_1^{e_1} \cdots p_n^{e_n})$ such that
each $p_i$ is irreducible, the $p_i$'s have no common factors, and
$$
p = c\;\prod_{i=1}^n p_i^{e_i}\,.
$$
}
#endif
		fractionalRoots: % -> GN FRR;
		roots: % -> GN FRR;
#if ALDOC
\aspage{fractionalRoots,roots}
\astarget{fractionalRoots}
\astarget{roots}
\Usage{ fractionalRoots~p\\ roots~p }
\Signature{\%}{\astype{Generator} \astype{FractionalRoot} \%}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns a generator that produces all the roots $p$
either in the ring or in its fraction field.}
#endif
	}
	if R has RationalRootRing then {
		RationalRootRing;
		if R has GcdDomain then {
			dispersion: % -> Z;
			dispersion: (%, %) -> Z;
			integerDistances: % -> List Z;
			integerDistances: (%, %) -> List Z;
#if ALDOC
\aspage{dispersion,integerDistances}
\astarget{dispersion}
\astarget{integerDistances}
\Usage{ dispersion~p\\ dispersion(p, q)\\
integerDistances~p\\ integerDistances(p, q)}
\Signatures{
dispersion: & \% $\to$ \astype{Integer}\\
dispersion: & (\%,\%) $\to$ \astype{Integer}\\
integerDistances: & \% $\to$ \astype{List} \astype{Integer}\\
integerDistances: & (\%,\%) $\to$ \astype{List} \astype{Integer}\\
}
\Params{
{\em p} & \% & A nonzero polynomial\\
{\em q} & \% & A nonzero polynomial (optional)\\
}
\Retval{integerDistances(p, q) returns
all the integers $e \in \ZZ$ such that for each such $e$
there exists $\alpha$ in an algebraic closure of the fraction
field of $R$ such that $p(\alpha) = q(\alpha + e) = 0$,
while dispersion(p, q) returns $-1$ if
integerDistances(p, q) contains only elements strictly smaller than $0$,
its maximal nonnegative element otherwise.}
\Remarks{The parameter $q$ is optional for both functions,
its default value being $p$.}
#endif
		}
		integerRoots: % -> Generator RR;
		rationalRoots: % -> Generator RR;
#if ALDOC
\aspage{integerRoots,rationalRoots}
\astarget{integerRoots}
\astarget{rationalRoots}
\Usage{ integerRoots~p\\ rationalRoots~p }
\Signature{\%}{\astype{Generator} \astype{FractionalRoot} \astype{Integer}}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Return $[(r_1,e_1),\dots,(r_n,e_n)]$ where the $r_i$'s are
the integer or rational roots of $p$ and have multiplicity $e_i$.}
#endif
		minIntegerRoot: % -> Partial Z;
		maxIntegerRoot: % -> Partial Z;
#if ALDOC
\aspage{minIntegerRoot,maxIntegerRoot}
\astarget{minIntegerRoot}
\astarget{maxIntegerRoot}
\Usage{ minIntegerRoot~p\\ maxIntegerRoot~p }
\Signature{\%}{\astype{Partial} \astype{Integer}}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{ Return \failed if $p$ has no integer root, its smallest (resp.~largest)
one otherwise.}
#endif
		if R has GcdDomain then {
			universalBound: (%, %) -> List Cross(%, Z);
#if ALDOC
\aspage{universalBound}
\Usage{\name(a, b)}
\Signature{(\%,\%)}{\astype{List} \builtin{Cross}(\%, \astype{Integer})}
\Params{ {\em a, b} & \% & Nonzero polynomials\\ }
\Retval{Return $[(p_1,e_1),\dots,(p_n,e_n)]$ such that any polynomial
bounded by $a$ and $b$ (in the sense of S.A.~Abramov,
{\em Rational solutions of linear difference and $q$--difference equations
with polynomial coefficients}, Proceedings of ISSAC'95)
must be a factor of $u = \prod_{i=1}^n \prod_{j=0}^{e_i} p_i(x-j)$.}
#endif
		}
	}
	default {
		local gcd?:Boolean == R has GcdDomain;

		if R has IntegralDomain then {
			resultant(p:%, q:%):R == resultant(p, q)$RES;
		}

		if R has GcdDomain then {
			local gcdproject(P:UPC0, p:P):% == {
				import from Z;
				assert(~zero? p);
				q:% := 0;
				for i in 0..degree p repeat
					q := gcd(q, project(P, p, i));
				q;
			}

-- TEMPORARY: WHEN algebraic extensions have good gcd algorithms
#if MULTIGCD
			gcd(l:List %):% == {
				import from MultiGcd(R pretend GcdDomain, %);
				(g, lq) := multiGcd l;
				g;
			}

			gcdquo(l:List %):(%, List %) == {
				import from MultiGcd(R pretend GcdDomain, %);
				multiGcd l;
			}
#endif

			local ugring?:Boolean	== R has UnivariateGcdRing;
			local field?:Boolean	== R has Field;
			local infCharp?:Boolean == R has FiniteCharacteristic
							and ~(R has FiniteSet);

			gcd(p:%, q:%):%	== {
				ugring? => ugGcd(p, q);
				field? => eucl(p, q);
				subResultantGcd(p, q)$RES;
			};

			-- destroys p and q
			gcd!(p:%, q:%):% == {
				ugring? => ugGcd!(p, q);
				field? => eucl!(p, q);
				subResultantGcd(p, q)$RES;
			}

			squareFree(p:%):(R, Product %) == {
				import from Integer,
					UnivariatePolynomialSquareFree(R
						 pretend GcdDomain, %);
				infCharp? => musser p;
				yun p;
			}

			if R has UnivariateGcdRing then {
				local ugGcd(p:%, q:%):% == {
					import from R;
					gcdUP(%)(p, q);
				}

				local ugGcd!(p:%, q:%):% == {
					import from R;
					gcdUP!(%)(p, q);
				}

				gcdquo(p:%, q:%):(%, %, %) == {
					import from R;
					gcdquoUP(%)(p, q);
				}
			}

			if R has Field then {
				local eucl(p:%, q:%):%	== monic euclid(p, q);
				local eucl!(p:%, q:%):%	== monic! euclid!(p, q);
			}
		}

		if R has FactorizationRing then {
			factor(p:%):(R, Product %)	== (factor(%)$R)(p);
			roots(p:%):GN FRR		== (roots(%)$R)(p);
			fractionalRoots(p:%):GN FRR== (fractionalRoots(%)$R)(p);
		}

		if R has RationalRootRing then {
			integerRoots(p:%):GN RR  == (integerRoots(%)$R)(p);
			rationalRoots(p:%):GN RR == (rationalRoots(%)$R)(p);
			minIntegerRoot(p:%):Partial Z == zselect(p, <$Z);
			maxIntegerRoot(p:%):Partial Z == zselect(p, >$Z);

			local zselect(p:%, f?: (Z, Z) -> Boolean):Partial Z == {
				import from Boolean, RR;
				assert(~zero? p);
				emp? := true;
				n:Z := 0;
				for r in integerRoots p repeat {
					m := integralValue r;
					if emp? or f?(m, n) then n := m;
					emp? := false;
				}
				emp? => failed;
				[n];
			}

			if R has GcdDomain then {
				dispersion(p:%):Z == disp integerDistances p;

				dispersion(p:%, q:%):Z ==
					disp integerDistances(p, q);

				local disp(l:List Z):Z == {
					empty? l => -1;
					m := first l;
					for n in rest l repeat
						if n > m then m := n;
					m < 0 => -1;
					m;
				}

				universalBound(a:%, b:%):List Cross(%, Z) == {
					import from Boolean, Z, List Z, R;
					assert(~zero? a); assert(~zero? b);
					u:List Cross(%, Z) := empty;
					l := [e for e in integerDistances(a,b)|_
						e >= 0];
					empty? l => u;
					spr := reverse! sort! l;
					lastm := next first spr;
					for m in spr repeat {
						assert(m >= 0);
						assert(m < lastm);
						bm := translate(b, (-m)::R);
						g := primitivePart gcd(a, bm);
						if degree g > 0 then {
							a := quotient(a, g);
							gm := translate(g,m::R);
							b := quotient(b, gm);
							u := cons((g, m), u);
						}
					}
					u;
				}
			}

			local roots(P:UPC0, p:P, f:% -> GN RR):GN RR ==
				f project(P, p);

			integerRoots(P:UPC0):P -> GN RR ==
				(p:P):GN(RR) +-> roots(P, p, integerRoots$%);

			rationalRoots(P:UPC0):P -> GN RR ==
				(p:P):GN(RR) +-> roots(P, p, rationalRoots$%);


			local project(P:UPC0, p:P):% == {
				import from Z;
				zero? p => 0;
				-- TEMPORARY: WOULD LIKE TO CACHE THE TEST
				-- gcd? => gcdproject(P, p);
				R has GcdDomain => gcdproject(P, p);
				q:% := 1;
				for i in 0..degree p repeat
					q := times!(q, project(P, p, i));
				q;
			}

			local project(P:UPC0, p:P, m:Z):% == {
				q:% := 0;
				for term in p repeat {
					(c, n) := term;
					q := add!(q, coefficient(c, m), n);
				}
				q;
			}
		}
	}
}
