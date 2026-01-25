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
----------------------------- zring.as ----------------------------------
#include "sumit"

macro {
	Z  == Integer;
	RR == RationalRoot;
}

#if ASDOC
\thistype{RationalRoot}
\History{Manuel Bronstein}{11/12/96}{created}
\Usage{import from \this}
\Descr{\this~provides rational numbers with multiplicities.}
\begin{exports}
integer?: & \% $\to$ Boolean & Test whether root is an integer\\
integerRoot: & (Integer, Integer) $\to$ \% & Create a root\\
integerValue: & \% $\to$ Integer & Value of an integer root\\
multiplicity: & \% $\to$ Integer & Multiplicity of a root\\
rationalRoot: & (Integer, Integer, Integer) $\to$ \% & Create a root\\
setMultiplicity!: & (\%, Integer) $\to$ \% & Change a multiplicity\\
value: &  \% $\to$ (Integer, Integer) & Value of a root\\
\end{exports}
#endif

RationalRoot: SumitType with {
	integer?: % -> Boolean;
#if ASDOC
\aspage{integer?}
\Usage{\name~r}
\Params{ {\em r} & \this & A root\\ }
\Retval{Return \true~if r is an integer, \false~otherwise.}
#endif
	integerRoot: (Z, Z) -> %;
#if ASDOC
\aspage{integerRoot}
\Usage{ \name(n, m) }
\Signature{(Integer, Integer)}{\this}
\Params{
{\em n} & Integer & A root\\
{\em m} & Integer & Its multiplicity\\
}
\Retval{Return the root $n$ with multiplicity $m$.}
\seealso{rationalRoot(\this)}
#endif
	integerValue: % -> Z;
#if ASDOC
\aspage{integerValue}
\Usage{ \name~r }
\Signature{\this}{Integer}
\Params{ {\em r} & \this & A root\\ }
\Retval{Returns the value of the integer root $r$, ignoring its multiplicity.}
\seealso{value(\this)}
#endif
	multiplicity: % -> Z;
#if ASDOC
\aspage{multiplicity}
\Usage{ \name~r }
\Signature{\this}{Integer}
\Params{ {\em r} & \this & A root\\ }
\Retval{Return the multiplicity of $r$.}
#endif
	rationalRoot: (Z, Z, Z) -> %;
#if ASDOC
\aspage{rationalRoot}
\Usage{ \name(n, d, m) }
\Signature{(Integer, Integer, Integer)}{\this}
\Params{
{\em n} & Integer & A numerator\\
{\em d} & Integer & A denominator\\
{\em m} & Integer & A multiplicity\\
}
\Retval{Return the root $n/d$ with multiplicity $m$.}
\seealso{integerRoot(\this)}
#endif
	setMultiplicity!: (%, Z) -> %;
#if ASDOC
\aspage{setMultiplicity!}
\Usage{ \name(r, m) }
\Signature{(\this, Integer)}{Integer}
\Params{
{\em r} & \this & A root\\
{\em m} & Integer & Its new multiplicity\\
}
\Descr{Sets the multiplicity of $r$ to $m$ and returns $r$.}
#endif
	value: % -> (Z, Z);
#if ASDOC
\aspage{value}
\Usage{ (n, d) := \name~r }
\Signature{\this}{(Integer, Integer)}
\Params{ {\em r} & \this & A root\\ }
\Retval{Return $(n, d)$ such that the value of $r$ is $n/d$.}
\seealso{integerValue(\this)}
#endif
} == add {
	macro Rep == Record(num:Z, den:Z, mult:Z);

	import from Z, Rep;

	sample:%			== per [0, 1, 1];
	value(r:%):(Z, Z)		== (numerator r, denominator r);
	integerValue(r:%):Z		== { ASSERT(integer? r); numerator r }
	multiplicity(r:%):Z		== rep(r).mult;
	integerRoot(n:Z, e:Z):%		== { ASSERT(e > 0); per [n, 1, e] }
	integer?(r:%):Boolean		== one? denominator r;
	local numerator(r:%):Z		== rep(r).num;
	local denominator(r:%):Z	== rep(r).den;

	rationalRoot(n:Z, d:Z, e:Z):% == {
		ASSERT(e > 0);
		zero? n => per [0, 1, 1];
		(g, nn, dd) := gcdquo(n, d);
		dd < 0 => per [-nn, -dd, e];
		per [nn, dd, e];
	}

	(a:%) = (b:%):Boolean ==
		numerator(a) = numerator(b) and
			denominator(a) = denominator(b) and
				multiplicity(a) = multiplicity(b);

	extree(r:%):ExpressionTree == {
		import from List ExpressionTree;
		ExpressionTreeList [extree value r, extree multiplicity r];
	}

	local extree(n:Z, d:Z):ExpressionTree == {
		import from List ExpressionTree;
		tnum := extree n;
		one? d => tnum;
		ExpressionTreeQuotient [tnum, extree d];
	}

	setMultiplicity!(r:%, e:Z):% == {
		ASSERT(e > 0);
		rep(r).mult := e;
		r;
	}
}

#if ASDOC
\thistype{RationalRootRing}
\History{Manuel Bronstein}{10/12/96}{created}
\Usage{\this: Category}
\Descr{\this~is the category of gcd domains that export an algorithm for
finding the rational roots of univariate polynomials over themselves.}
\begin{exports}
integerRoots: & (P:POL \%) $\to$ P $\to$ List RationalRoot & Integer roots\\
rationalRoots: & (P:POL \%) $\to$ P $\to$ List RationalRoot & Rational roots\\
\end{exports}
\begin{aswhere}
POL &==& UnivariatePolynomialCategory0\\
\end{aswhere}
#endif

RationalRootRing: Category == SumitRing with {
	integerRoots: (P: UnivariatePolynomialCategory0 %) -> P -> List RR;
#if ASDOC
\aspage{integerRoots}
\Usage{ \name(P)(p) }
\Signature{(P: UnivariatePolynomialCategory0 \%)}{P $\to$ List RationalRoot}
\Params{
{\em P} & UnivariatePolynomialCategory0 \% & A polynomial type\\
{\em p} & P & A polynomial\\
}
\Retval{Return $[(r_1,e_1),\dots,(r_n,e_n)]$ where the $r_i$'s are
the integer roots of $p$ and have multiplicity $e_i$.}
#endif
	rationalRoots: (P: UnivariatePolynomialCategory0 %) -> P -> List RR;
#if ASDOC
\aspage{rationalRoots}
\Usage{ \name(P)(p) }
\Signature{(P: UnivariatePolynomialCategory0 \%)}{P $\to$ List RationalRoot}
\Params{
{\em P} & UnivariatePolynomialCategory0 \% & A polynomial type\\
{\em p} & P & A polynomial\\
}
\Retval{Return $[(r_1,e_1),\dots,(r_n,e_n)]$ where the $r_i$'s are
the rational roots of $p$ and have multiplicity $e_i$.}
#endif
	default integerRoot(P:UnivariatePolynomialCategory0 %)(p:P):List RR == {
		import from RR;
		l:List RR := empty();
		for rt in rationalRoots(P)(p) repeat
			if integer? rt then l := cons(rt, l);
		l;
	}
}

