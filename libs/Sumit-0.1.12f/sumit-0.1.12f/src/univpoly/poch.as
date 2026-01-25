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
--------------------------- poch.as ----------------------------
#include "sumit"

#if ASDOC
\thistype{GeneralizedPochammerMonomial}
\History{Manuel Bronstein}{4/12/95}{created}
\Usage{import from \this~R}
\Params{ {\em R} & CommutativeRing & the coefficients\\ }
\Descr{\this~R implements the generalized Pochammer monomials,
of the form $c \gpoch{x}{a}{n}{e}$, where $c \in R$ and
$\gpoch{x}{a}{n}{e}$ is the
generalized Pochammer symbol defined by
$$
\gpoch{x}{a}{n}{e} = \prod_{i=0}^{n-1} (x + (i + a) e)
= (x + a e) (x + (a+1) e) \cdots (x + (a+n-1) e)\;.
$$
}
\begin{exports}
\category{Order}\\
$*$: & (R, \%) $\to$ \% & Multiplication by a scalar\\
$-$: & \% $\to$ \% & Negation of a monomial\\
coefficient: & \% $\to$ R & Coefficient of a monomial\\
degree: & \% $\to$ Z & Degree of a monomial\\
expand: & (\%, P:POLY) $\to$ P & Conversion to a polynomial\\
integerRoots: & \% $\to$ List Z & Roots of a monomial\\
monomial: & (R, Z, Z, Z) $\to$ \% & Creation of a monomial\\
pochammer: & (Z, Z, Z, P:POLY) $\to$ P &
Expansion of a generalized Pochammer symbol\\
shift: & \% $\to$ Z & Increment of the generalized Pochammer symbol\\
shift: & (\%, Z) $\to$ Z & Translate the independent variable\\
shift!: & (\%, Z) $\to$ Z & Translate the independent variable\\
start: & \% $\to$ Z & First offset of the generalized Pochammer symbol\\
valuesDown: & (\%, R) $\to$ Generator R & Generate values\\
valuesUp: & (\%, R) $\to$ Generator R & Generate values\\
zero?: & \% $\to$ Boolean & Test whether a monomial is 0\\
\end{exports}
\Aswhere{
Z &==& Integer\\
POLY &==& UnivariatePolynomialCategory R\\
}
#endif

macro {
	ARR == PrimitiveArray;
	Z == Integer;
}

GeneralizedPochammerMonomial(R:CommutativeRing): Order with {
        *: (R, %) -> %;
#if ASDOC
\aspage{$*$}
\Usage{ c~\name~m }
\Signature{(R,\%)}{\%}
\Params{
{\em c} & R & An element of the coefficient ring\\
{\em m} & \% & A generalized Pochammer monomial\\
}
\Retval{Returns $c m$.}
#endif
	-: % -> %;
#if ASDOC
\aspage    {-}
\Usage     {\name~m}
\Signature {\%}{\%}
\Params{ {\em m} & \% & A generalized Pochammer monomial\\ }
\Retval{Returns $-m$.}
#endif
	coefficient: % -> R;
#if ASDOC
\aspage{coefficient}
\Usage{\name~m}
\Signature{\%}{R}
\Params{ {\em m} & \% & A generalized Pochammer monomial\\ }
\Retval{Returns the coefficient of $m$,
\ie $c$ where $m = c \gpoch{x}{a}{n}{e}$.}
#endif
	degree: % -> Z;
#if ASDOC
\aspage{degree}
\Usage{\name~m}
\Signature{\%}{Integer}
\Params{ {\em m} & \% & A generalized Pochammer monomial\\ }
\Retval{Returns the degree of $m$, $0$ if $m = 0$.}
#endif
	expand: (%, P:UnivariatePolynomialCategory R) -> P;
#if ASDOC
\aspage{expand}
\Usage{\name(m, P)}
\Signature{(\%, P:UnivariatePolynomialCategory R)}{P}
\Params{
{\em m} & \% & A generalized Pochammer monomial\\
{\em P} & UnivariatePolynomialCategory R & A polynomial type\\
}
\Retval{Returns the expansion of $m$, \ie
$$
m = c \gpoch{x}{a}{n}{e}
= c\; (x + a e) (x + (a+1) e) \cdots (x + (a+n-1) e)
$$
as an element of $P$.}
\seealso{pochammer(\this)}
#endif
	integerRoots: % -> List Z;
#if ASDOC
\aspage{integerRoots}
\Usage{\name~m}
\Signature{\%}{List Integer}
\Params{ {\em m} & \% & A generalized Pochammer monomial\\ }
\Retval{Returns all the integer roots of m,
\ie $\{- a e, - 2 a e, \dots, (1 - d) a e\}$ where
$m = c \gpoch{x}{a}{n}{e}$ and $c \ne 0$.}
#endif
	monomial: (R, Z, Z, Z) -> %;
#if ASDOC
\aspage{monomial}
\Usage{\name(c, a, n, e)}
\Signature{(R, Integer, Integer, Integer)}{\%}
\Params{
{\em c} & R & The coefficient\\
{\em a} & Integer & The offset\\
{\em n} & Integer & The degree\\
{\em e} & Integer & The shift\\
}
\Retval{Returns $c \gpoch{x}{a}{n}{e}$.}
#endif
	pochammer: (Z, Z, Z, P:UnivariatePolynomialCategory R) -> P;
#if ASDOC
\aspage{pochammer}
\Usage{\name(a, n, e, P)}
\Signature{(Integer, Integer, Integer, P:UnivariatePolynomialCategory R)}{P}
\Params{
{\em a} & Integer & The offset\\
{\em n} & Integer & The degree\\
{\em e} & Integer & The shift\\
{\em P} & UnivariatePolynomialCategory R & A polynomial type\\
}
\Retval{Returns
$$
\gpoch{x}{a}{n}{e}
= (x + a e) (x + (a+1) e) \cdots (x + (a+n-1) e)
$$
as an element of $P$.}
\seealso{expand(\this)}
#endif
	shift: % -> Z;
	shift: (%, Z) -> %;
	shift!: (%, Z) -> %;
#if ASDOC
\aspage{shift}
\Usage{ \name~m \\ \name(m, k) \\ \name!(m, k) }
\Signatures{
\name: & \% $\to$ Integer\\
\name: & (\%, Integer) $\to$ \%\\
\name!: & (\%, Integer) $\to$ \%\\
}
\Params{
{\em m} & \% & A generalized Pochammer monomial\\
{\em k} & Integer & The amount of shift\\
}
\Retval{
\name~m returns the shift of m, \ie $e$ where $m = c \gpoch{x}{a}{n}{e}$.\\
\name(m, k) and \name!(m, k) both return p shifted the $k e$ times, \ie
$$
E^{ke} \paren{c \gpoch{x}{a}{n}{e}} = c \gpoch{x}{a+k}{i}{e}
$$
where
\name!(m, k) is allowed to destroy or reuse the storage used by m,
so m is lost after that call.}
\Remarks{This function may cause m to be destroyed, so do not use it unless
m has been locally allocated, and is guaranteed not to share space
with other elements. Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
#endif
	start: % -> Z;
#if ASDOC
\aspage{start}
\Usage{\name~m}
\Signature{\%}{Integer}
\Params{ {\em m} & \% & A generalized Pochammer monomial\\ }
\Retval{Returns the offset of $m$, \ie $a$ where $m = c \gpoch{x}{a}{n}{e}$.}
#endif
	valuesDown: (%, R) -> Generator R;
#if ASDOC
\aspage{valuesDown}
\Usage{\name(m, n)}
\Signature{(\%,R)}{Generator R}
\Params{
{\em m} & \% & A generalized Pochammer monomial\\
{\em n} & R & A scalar\\
}
\Retval{Returns a generator generating the
sequence $m(n), m(n-e), m(n-2e),\ldots$ where $e$ is the shift of $m$.}
\seealso{valuesUp(\this)}
#endif
	valuesUp: (%, R) -> Generator R;
#if ASDOC
\aspage{valuesUp}
\Usage{\name(m, n)}
\Signature{(\%,R)}{Generator R}
\Params{
{\em m} & \% & A generalized Pochammer monomial\\
{\em n} & R & A scalar\\
}
\Retval{Returns a generator generating the
sequence $m(n), m(n+e), m(n+2e),\ldots$ where $e$ is the shift of $m$.}
\seealso{valuesDown(\this)}
#endif
	zero?: % -> Boolean;
#if ASDOC
\aspage{zero?}
\Usage{\name~m}
\Signature{\%}{Boolean}
\Params{ {\em m} & \% & A generalized Pochammer monomial\\ }
\Retval{Returns \true~if $m = 0$, \false~otherwise.}
#endif
} == add {
	macro Rep == Record(coef: R, deg: Z, frum: Z, shft: Z);

	import from Z, Rep;

	monomial(a:R, m:Z, d:Z, e:Z):%	== per [a, d, m, e];
	sample:%			== per [1, 0, 0, 0];
	degree(m:%):Z			== rep(m).deg;
	start(m:%):Z			== rep(m).frum;
	shift(m:%):Z			== rep(m).shft;
	coefficient(m:%):R		== rep(m).coef;
	shift!(m:%, k:Z):%		== { rep(m).frum := k + start m; m; }
	(m1:%) > (m2:%):Boolean		== degree m1 > degree m2;
	zero?(m:%):Boolean	== { import from R; zero? coefficient m; }

	-(m:%):% == {
		import from R;
		monomial(- coefficient m, start m, degree m, shift m);
	}

	(c:R) * (m:%):%	== {
		import from R;
		monomial(c * coefficient m, start m, degree m, shift m);
	}

	expand(m:%, P:UnivariatePolynomialCategory R):P == {
		times!(coefficient m, pochammer(start m, degree m, shift m, P));
	}

	valuesUp(m:%, n:R):Generator R == {
		import from SingleInteger, Z, ARR R;
		c := coefficient m;
		zero? c or zero?(d := degree m) => generate { repeat yield c };
		arr:ARR R := new(dd := retract d);
		e := shift(m)::R;
		val := arr.1 := n + start(m) * e;
		for i in 2..dd repeat {
			arr.i := arr(prev i) + e;
			val := val * arr.i;
		}
		val := c * val;
		generate {
			repeat {
				yield val;
				t := arr.dd + e;
				val := {
					zero? t => 0;
					zero?(arr.1) => c * t * prod(arr,2,dd);
					quotient(val * t, arr.1);
				}
				for i in 2..dd repeat arr(prev i) := arr.i;
				arr.dd := t;
			}
		}
	}

	valuesDown(m:%, n:R):Generator R == {
		import from SingleInteger, Z, ARR R;
		c := coefficient m;
		zero? c or zero?(d := degree m) => generate { repeat yield c };
		arr:ARR R := new(dd := retract d);
		e := shift(m)::R;
		val := arr.1 := n + start(m) * e;
		for i in 2..dd repeat {
			arr.i := arr(prev i) + e;
			val := val * arr.i;
		}
		val := c * val;
		generate {
			repeat {
				yield val;
				t := arr.1 - e;
				val := {
					zero? t => 0;
					zero?(arr.dd) =>c*t*prod(arr,1,prev dd);
					quotient(val * t, arr.dd);
				}
				for i in 2..dd repeat arr.i := arr(prev i);
				arr.1 := t;
			}
		}
	}

	local prod(a:ARR R, n:SingleInteger, m:SingleInteger):R == {
		x:R := 1;
		for i in n..m repeat x := times!(x, a.i);
		x;
	}

	integerRoots(m:%):List Z == {
		ASSERT(~zero? m);
		minusE := - shift m;
		[i * minusE for i in start m .. start m + degree m - 1];
	}

	shift(m:%, k:Z):% == {
		monomial(coefficient m, k + start m, degree m, shift m);
	}

	(p:TextWriter) << (m:%):TextWriter == {
		p << "gPochMononial(" << coefficient m << ", ";
		p << start m << ", " << degree m << " | " << shift m << ")";
	}

	(m1:%) = (m2:%):Boolean == {
		import from R;
		coefficient m1 = coefficient m2 and start m1 = start m2
			and degree m1 = degree m2 and shift m1 = shift m2;
	}

	pochammer(a:Z, d:Z, e:Z, P:UnivariatePolynomialCategory R):P == {
		x:P := monom;
		p:P := 1;
		ee := e::P;
		for i in a .. a + d - 1 repeat p := times!(p, x + i * ee);
		p;
	}
}
