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
----------------------------- sit_sercat.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I == MachineInteger;
	Z == Integer;
	UPC == UnivariatePolynomialCategory;
}

#if ALDOC
\thistype{UnivariateTaylorSeriesCategory}
\History{Manuel Bronstein}{6/6/2000}{created}
\Usage{\this~R: Category}
\Params{
{\em R} & \astype{SumitType} & The coefficient domain\\
        & \astype{ArithmeticType} &\\
}
\Descr{\this~R is the category of univariate Taylor series with coefficients
in R.}
\begin{exports}
\category{\astype{UnivariateFreeAlgebra} R}\\
\asexp{degree}:
& \% $\to$ \astype{Partial} \astype{Integer} & upper bound on the degree\\
\asexp{expand}:
& (Rx: UPC R, R) $\to$ Rx $\to$ \% & series expansion around a point\\
\asexp{finite?}:
& \% $\to$ \astype{Boolean} & check whether the support is finite\\
\asexp{series}: & \astype{Sequence} R $\to$ \% & creation of a series\\
\end{exports}
\begin{aswhere}
UPC &== UnivariatePolynomialCategory\\
\end{aswhere}
\begin{exports}[if $R$ has \astype{CommutativeRing} then]
\asexp{differentiate}: & \% $\to$ \% & Differentiation\\
& (\%, \astype{Integer}) $\to$ \% & \\
\end{exports}
\begin{exports}
[if $R$ has \astype{CommutativeRing} and $R$ has \astype{QRing} then]
\asexp{integrate}: & \% $\to$ \% & Integration\\
 & (\%, \astype{Integer}) $\to$ \% & \\
\end{exports}
#endif

define UnivariateTaylorSeriesCategory(R:Join(ArithmeticType, SumitType)):
	Category == UnivariateFreeAlgebra R with {
		degree: % -> Partial Z;
		finite?: % -> Boolean;
#if ALDOC
\aspage{degree,finite?}
\astarget{degree}
\astarget{finite?}
\Usage{degree~s\\finite?~s}
\Signatures{
degree: & \% $\to$ \astype{Partial} \astype{Integer} \\
finite?: & \% $\to$ \astype{Boolean}\\
}
\Params{ {\em s} & \% & a series\\ }
\Retval{finite?(s) returns \true if s is known
to have finite support and \false otherwise, while
degree(s) returns $[n]$ if s is known
to have finite support and $\deg(s) \le n = 0$, \failed otherwise.}
#endif
		if R has CommutativeRing then {
			differentiate: % -> %;
			differentiate: (%, Integer) -> %;
			if R has QRing then {
				integrate: % -> %;
				integrate: (%, Integer) -> %;
			}
#if ALDOC
\aspage{differentiate,integrate}
\astarget{differentiate}
\astarget{integrate}
\Usage{differentiate~s\\ differentiate(s, n)\\ integrate~s}
\Signatures{
\name: & \% $\to$ \%\\
\name: & (\%, \astype{Integer}) $\to$ \%\\
}
\Params{
{\em s} & \% & a series\\
{\em n} & \astype{Integer} & The order of differentiation or integration\\
}
\Retval{differentiate(s), differentiate(s, n), integrate(s) and
integrate(s, n) return respectively $ds/dx$, $d^n s/dx^n$,
$\int s(x)dx$ and $\int \dots \int s(x) dx^n$.
}
#endif
}
		expand: (Rx:UPC R, R) -> Rx -> %;
#if ALDOC
\aspage{expand}
\Usage{\name(Rx,a)\\ \name(Rx,a)(p)}
\Signature{(Rx:\astype{UnivariatePolynomialCategory} R, Rx)}{Rx $\to$ \%}
\Params{
{\em Rx} & \astype{UnivariatePolynomialCategory} R & a polynomial type\\
{\em a} & R & the expansion point\\
{\em p} & Rx & a polynomial\\
}
\Retval{\name(Rx,a)(p) returns the series expansion of $p$ around $a$.}
#endif
		series: Sequence R -> %;
#if ALDOC
\aspage{series}
\Usage{\name~s}
\Signature{\astype{Sequence} R}{\%}
\Params{ {\em s} & \astype{Sequence} R & a coefficient sequence\\ }
\Retval{Returns $s$ viewed as a series.}
#endif
		default {
			if R has CommutativeRing then {
				if R has QRing then {
					integrate(s:%):% == {
						import from Z;
						integrate(s, 1);
					}
				}

				differentiate(s:%):% == {
					import from Z;
					differentiate(s, 1);
				}
			}

			expand(Rx:UPC R, a:R):Rx -> % == {
				f := coeffs(Rx, a);
				(p:Rx):% +-> {
					import from I,Z,R,Sequence R,Stream R;
					zero? p => 0;
					series sequence stream(f p,
						next machine degree p, 0);
				}
			}

			local coeffs(Rx:UPC R, a:R):Rx -> Generator R == {
				zero? a => {
					(p:Rx):Generator R +-> coefficients p;
				 }
				(p:Rx):Generator R +-> generate {
					import from Boolean, I, Z;
					assert(~zero? p);
					for i in 0..machine degree p repeat {
						(p, c) := Horner(p, a);
						yield c;
					}
				}
			}

			(s:%)^(n:I):% == {
				import from BinaryPowering(%, I);
				binaryExponentiation(s, n);
			}
		}
}

