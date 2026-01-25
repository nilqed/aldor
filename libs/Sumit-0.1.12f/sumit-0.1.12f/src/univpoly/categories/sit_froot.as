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
----------------------------- sit_froot.as ----------------------------------
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
\thistype{FractionalRoot}
\History{Manuel Bronstein}{11/12/96}{created RationalRoot}
\History{Manuel Bronstein}{17/8/2000}{added the parameter R, changed type name}
\Usage{import from \this}
\Descr{\this(R) provides fractions of R with multiplicities.}
\Params{ {\em R} & \astype{CommutativeRing} & A ring\\ }
\begin{exports}
\category{SumitType}\\
\asexp{fractionalRoot}: & (R, R, \astype{Integer}) $\to$ \% & Create a root\\
\asexp{integral?}:
& \% $\to$ \astype{Boolean} & Test whether root is integral\\
\asexp{integralRoot}: & (R, \astype{Integer}) $\to$ \% & Create a root\\
\asexp{integralValue}: & \% $\to$ R & Value of an integral root\\
\asexp{multiplicity}: & \% $\to$ \astype{Integer} & Multiplicity of a root\\
\asexp{setMultiplicity!}:
& (\%, \astype{Integer}) $\to$ \% & Change a multiplicity\\
\asexp{value}: &  \% $\to$ (R, R) & Value of a root\\
\end{exports}
#endif

FractionalRoot(R:CommutativeRing): SumitType with {
	integral?: % -> Boolean;
#if ALDOC
\aspage{integral?}
\Signature{\%}{\astype{Boolean}}
\Usage{\name~r}
\Params{ {\em r} & \% & A root\\ }
\Retval{Return \true~if r is in R, \false~otherwise.}
#endif
	integralRoot: (R, Z) -> %;
	fractionalRoot: (R, R, Z) -> %;
#if ALDOC
\aspage{fractionalRoot,integralRoot}
\astarget{fractionalRoot}
\astarget{integralRoot}
\Usage{fractionalRoot(a, b, n)\\ integralRoot(a, n)}
\Signatures{
fractionalRoot: & (R, \astype{Integer}, \astype{Integer}) $\to$ \%\\
integralRoot: & (R, \astype{Integer}) $\to$ \%\\
}
\Params{
{\em a} & R & A numerator\\
{\em b} & R & A denominator\\
{\em n} & \astype{Integer} & A multiplicity\\
}
\Retval{Return the root $a$ or $a/b$ with multiplicity $n$.}
#endif
	integralValue: % -> R;
#if ALDOC
\aspage{integralValue}
\Usage{ \name~r }
\Signature{\%}{\astype{Integer}}
\Params{ {\em r} & \% & A root\\ }
\Retval{Returns the value of the integral root $r$, ignoring its multiplicity.}
\seealso{\asexp{value}}
#endif
	multiplicity: % -> Z;
#if ALDOC
\aspage{multiplicity}
\Usage{ \name~r }
\Signature{\%}{\astype{Integer}}
\Params{ {\em r} & \% & A root\\ }
\Retval{Return the multiplicity of $r$.}
#endif
	setMultiplicity!: (%, Z) -> %;
#if ALDOC
\aspage{setMultiplicity!}
\Usage{ \name(r, m) }
\Signature{(\%, \astype{Integer})}{\astype{Integer}}
\Params{
{\em r} & \% & A root\\
{\em m} & \astype{Integer} & Its new multiplicity\\
}
\Descr{Sets the multiplicity of $r$ to $m$ and returns $r$.}
#endif
	value: % -> (R, R);
#if ALDOC
\aspage{value}
\Usage{ (n, d) := \name~r }
\Signature{\%}{(\astype{Integer}, \astype{Integer})}
\Params{ {\em r} & \% & A root\\ }
\Retval{Return $(n, d)$ such that the value of $r$ is $n/d$.}
\seealso{\asexp{integralValue}}
#endif
} == add {
	Rep == Record(num:R, den:R, mult:Z);

	import from Z, R, Rep;

	value(r:%):(R, R)		== (numerator r, denominator r);
	integralValue(r:%):R		== { assert(integral? r); numerator r }
	multiplicity(r:%):Z		== rep(r).mult;
	integralRoot(n:R, e:Z):%	== { assert(e > 0); per [n, 1, e] }
	integral?(r:%):Boolean		== one? denominator r;
	local numerator(r:%):R		== rep(r).num;
	local denominator(r:%):R	== rep(r).den;

	if R has Field then {
		fractionalRoot(n:R, d:R, e:Z):% == {
			import from Boolean;
			assert(~zero? d); assert(e > 0);
			per [n/d, 1, e];
		}
	}
	else if R has GcdDomain then {
		fractionalRoot(n:R, d:R, e:Z):% == {
			import from Boolean;
			assert(~zero? d); assert(e > 0);
			zero? n => per [0, 1, e];
			(g, nn, dd) := gcdquo(n, d);
			unit? dd => per [quotient(nn, dd), 1, e];
			per [nn, dd, e];
		}
	}
	else {
		fractionalRoot(n:R, d:R, e:Z):% == {
			import from Boolean, Partial R;
			assert(~zero? d); assert(e > 0);
			zero? n => per [0, 1, e];
			failed?(u := exactQuotient(n, d)) => per [n, d, e];
			per [retract u, 1, e];
		}
	}

	(a:%) = (b:%):Boolean ==
		numerator(a) = numerator(b) and
			denominator(a) = denominator(b) and
				multiplicity(a) = multiplicity(b);

	extree(r:%):ExpressionTree == {
		import from List ExpressionTree;
		ExpressionTreeList [extree value r, extree multiplicity r];
	}

	local extree(n:R, d:R):ExpressionTree == {
		import from List ExpressionTree;
		tnum := extree n;
		one? d => tnum;
		ExpressionTreeQuotient [tnum, extree d];
	}

	setMultiplicity!(r:%, e:Z):% == {
		assert(e > 0);
		rep(r).mult := e;
		r;
	}
}

