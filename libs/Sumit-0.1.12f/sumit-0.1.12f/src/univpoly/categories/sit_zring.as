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
----------------------------- sit_zring.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1996
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1996-97
-----------------------------------------------------------------------------

#include "sumit"

macro {
	Z  == Integer;
	RR == FractionalRoot Z;
	GEN== Generator;
}

#if ALDOC
\thistype{RationalRootRing}
\History{Manuel Bronstein}{10/12/96}{created}
\Usage{\this: Category}
\Descr{\this~is the category of gcd domains that export an algorithm for
finding the rational roots of univariate polynomials over themselves.}
\begin{exports}
\category{\astype{Ring}}\\
\asexp{integerRoots}:
& (P:POL \%) $\to$ P $\to$ \astype{Generator} FR \astype{Integer} &
Integer roots\\
\asexp{rationalRoots}:
& (P:POL \%) $\to$ P $\to$ \astype{Generator} FR \astype{Integer}&
Rational roots\\
\end{exports}
\begin{aswhere}
FR &==& \astype{FractionalRoot}\\
POL &==& \astype{UnivariatePolynomialCategory0}\\
\end{aswhere}
#endif

define RationalRootRing: Category == Ring with {
	integer: (P:UnivariatePolynomialCategory0 %) -> % -> Partial Z;
	integer?: (P:UnivariatePolynomialCategory0 %) -> % -> Boolean;
	rational: (P:UnivariatePolynomialCategory0 %) -> % ->Partial Cross(Z,Z);
	rational?: (P:UnivariatePolynomialCategory0 %) -> % -> Boolean;
	integerRoots: (P:UnivariatePolynomialCategory0 %) -> P -> GEN RR;
	rationalRoots: (P:UnivariatePolynomialCategory0 %) -> P -> GEN RR;
#if ALDOC
\aspage{integerRoots,rationalRoots}
\astarget{integerRoots}
\astarget{rationalRoots}
\Usage{ integerRoots(P)(p)\\ rationalRoots(P)(p) }
\Signature{(P: POL \%)}{P $\to$ \astype{Generator} \astype{RationalRoot}}
\begin{aswhere}
POL &==& \astype{UnivariatePolynomialCategory0}\\
\end{aswhere}
\Params{
{\em P} & \astype{UnivariatePolynomialCategory0} \% & A polynomial type\\
{\em p} & P & A polynomial\\
}
\Retval{Return $[(r_1,e_1),\dots,(r_n,e_n)]$ where the $r_i$'s are
the integer or rational roots of $p$ and have multiplicity $e_i$.}
#endif
	default {
		integer?(P:UnivariatePolynomialCategory0 %):% -> Boolean == {
			import from Boolean, Partial Z;
			f := integer P;
			(r:%):Boolean +-> ~failed? f r;
		}

		integer(P:UnivariatePolynomialCategory0 %):% -> Partial Z == {
			import from RR;
			zRoots := integerRoots P;
			x:P := monom;
			(r:%):Partial Z +-> {
				for z in zRoots(x - r::P) repeat
					return [integralValue z];
				failed;
			}
		}

		rational?(P:UnivariatePolynomialCategory0 %):% -> Boolean == {
			import from Boolean, Partial Cross(Z, Z);
			f := rational P;
			(r:%):Boolean +-> ~failed? f r;
		}

		rational(P:UnivariatePolynomialCategory0 %):
			% -> Partial Cross(Z, Z) == {
			import from RR;
			rRoots := rationalRoots P;
			x:P := monom;
			(r:%):Partial Cross(Z, Z) +-> {
				for z in rRoots(x-r::P) repeat return [value z];
				failed;
			}
		}

		integerRoot(P:UnivariatePolynomialCategory0 %):P -> GEN RR == {
			rRoots := rationalRoots P;
			(p:P):GEN RR +-> generate {
				import from RR;
				for z in rRoots p | integral? z repeat yield z;
			}
		}
	}
}

