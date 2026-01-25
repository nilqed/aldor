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
--------------------------- upoch.as ----------------------------
#include "sumit"

#if ASDOC
\thistype{GeneralizedPochammerUnivariatePolynomial}
\History{Manuel Bronstein}{5/12/95}{created}
\Usage{import from \this~R}
\Params{ {\em R} & CommutativeRing & the coefficients\\ }
\Descr{\this~R provides a compact implementation of univariate
polynomials in the form
$$
\sum_i a_i \gpoch{x}{a}{i}{e}
$$
where the $a_i$'s are in $R$, and $\gpoch{x}{a}{n}{e}$ is the
generalized Pochammer symbol defined by
$$
\gpoch{x}{a}{n}{e} = \prod_{i=0}^{n-1} (x + (i + a) e)
= (x + a e) (x + (a+1) e) \cdots (x + (a+n-1) e)\;.
$$
}
\begin{exports}
\category{SumitType}\\
$*$: & (R, \%) $\to$ \% & Multiplication by a scalar\\
$-$: & \% $\to$ \% & Negation of a polynomial\\
0: & \% & The polynomial 0\\
apply: & (\%, R) $\to$ R & Evaluate a polynomial\\
apply: & (\%, TREE) $\to$ TREE & Apply a polynomial to a tree\\
apply: & (TEXT, \%, String) $\to$ TEXT & Write a polynomial to a port\\
degree: & \% $\to$ Z & Degree of a polynomial\\
expand: & (\%, P:POLY) $\to$ P & Conversion to a polynomial\\
lowestTerm: & \% $\to$ POCH & Monomial of lowest degree\\
normalize: & \% $\to$ \% & Quotient by the lowest primitive monomial\\
generator: & \% $\to$ Generator POCH & Make an iterator\\
polynomial: & List POCH $\to$ \% & Creation of a polynomial\\
shift: & \% $\to$ Z & Common increment of all the monomials\\
shift: & (\%, Z) $\to$ Z & Translate the independent variable\\
shift!: & (\%, Z) $\to$ Z & Translate the independent variable\\
start: & \% $\to$ Z & Common offset of all the monomials\\
valuesDown: & (\%, R) $\to$ Generator R & Generate values\\
valuesUp: & (\%, R) $\to$ Generator R & Generate values\\
zero?: & \% $\to$ Boolean & Test whether a polynomial is 0\\
\end{exports}
\Aswhere{
POCH &==& GeneralizedPochammerMonomial R\\
POLY &==& UnivariatePolynomialCategory R\\
TEXT &==& TextWriter\\
TREE &==& ExpressionTree\\
}
\begin{exports}[if $R$ has RationalRootRing then]
integerRoots: & \% $\to$ List RationalRoot & Integer roots\\
rationalRoots: & \% $\to$ List RationalRoot & Rational roots\\
\end{exports}
#endif

macro {
	Z	== Integer;
	Rx	== SparseUnivariatePolynomial R;
	POCH	== GeneralizedPochammerMonomial R;
	TREE	== ExpressionTree;
	OPOCH	== ExpressionTreeGeneralizedPochammer;
	TEXT	== TextWriter;
	RR	== RationalRoot;
	Symbol	== String;
	anon	== "\Box";
}

GeneralizedPochammerUnivariatePolynomial(R:CommutativeRing,avar:Symbol == anon):
	SumitType with {
		*: (R, %) -> %;
#if ASDOC
\aspage{$*$}
\Usage{ c~\name~m }
\Signature{(R,\%)}{\%}
\Params{
{\em c} & R & An element of the coefficient ring\\
{\em p} & \% & A polynomial\\
}
\Retval{Returns $c p$.}
#endif
		-: % -> %;
#if ASDOC
\aspage    {-}
\Usage     {\name~m}
\Signature {\%}{\%}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns $-m$.}
#endif
		0:%;
#if ASDOC
\aspage{0}
\Usage{\name}
\Signature{}{\%}
\Retval{Returns $0$ as a polynomial.}
#endif
		apply: (%, R) -> R;
		apply: (%, TREE) -> TREE;
		apply: (TEXT, %, Symbol) -> TEXT;
#if ASDOC
\aspage{apply}
\Usage{ \name(p, a)\\ p~a\\ \name(p, t)\\p~t\\ \name(port, p, x)\\ port(p, x) }
\Signatures{
\name: & (\%, R) $\to$ R\\
\name: & (\%, ExpressionTree) $\to$ ExpressionTree\\
\name: & (TextWriter, \%, String) $\to$ TextWriter\\
}
\Params{
{\em p} & \% & A polynomial\\
{\em a} & R & A scalar\\
{\em t} & ExpressionTree & An expression tree\\
{\em port} & TextWriter & An output port\\
{\em x} & String & A name for the variable\\
}
\Retval{
\name(p, a) returns the result of evaluating $p$ on the scalar $a$.\\
\name(p, t) returns the result of evaluating $p$ on the expression tree $t$.\\
\name(port, p, x) sends p to port using x as the variable name,
and returns the output port afterwards.
}
#endif
		degree: % -> Z;
#if ASDOC
\aspage{degree}
\Usage{\name~p}
\Signature{\%}{Integer}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns the degree of $p$, \ie $n$ where
$$
p = \sum_{i=0}^n a_i \gpoch{x}{a}{i}{e}
$$
and $a_n \ne 0$.
Returns 0 if $p = 0$.}
#endif
		expand: (%, P:UnivariatePolynomialCategory R) -> P;
#if ASDOC
\aspage{expand}
\Usage{\name(p, P)}
\Signature{(\%, P:UnivariatePolynomialCategory R)}{P}
\Params{
{\em p} & \% & A polynomial\\
{\em P} & UnivariatePolynomialCategory R & A polynomial type\\
}
\Retval{Returns the expansion of $p$ as an element of $P$.}
#endif
		if R has RationalRootRing then integerRoots: % -> List RR;
#if ASDOC
\aspage{integerRoots}
\Usage{ \name~p }
\Signature{\%}{List RationalRoot}
\Params{ {\em p} & P & A polynomial\\ }
\Retval{Return $[(r_1,e_1),\dots,(r_n,e_n)]$ where the $r_i$'s are
the integer roots of $p$ and have multiplicity $e_i$.}
#endif
		generator: % -> Generator POCH;
#if ASDOC
\aspage{generator}
\Usage{ for m in p repeat \{ \dots \} }
\Signature{\%}{Generator GeneralizedPochammerMonomial R}
\Params{ {\em p} & \% & A polynomial\\ }
\Descr{This functions allows a polynomial to be iterated independently of its
representation. The generator yields monomials with increasing exponents
and nonzero coefficients.}
#endif
		lowestTerm: % -> POCH;
#if ASDOC
\aspage{lowestTerm}
\Usage{\name~p}
\Signature{\%}{GeneralizedPochammerMonomial R}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns the monomial of lowest degree in $p$,
\ie $a_m \gpoch{x}{a}{m}{e}$ where
$$
p = \sum_{i=m}^n a_i \gpoch{x}{a}{i}{e}
$$
and $a_m \ne 0$.
Returns 0 if $p = 0$.}
#endif
		normalize: % -> %;
#if ASDOC
\aspage{normalize}
\Usage{\name~p}
\Signature{\%}{\%}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns the quotient of $p$ by its normalized lower term, \ie
$$
\sum_{i=m}^n a_i \gpoch{x}{a+m}{i-m}{e}
$$
where
$$
p = \sum_{i=m}^n a_i \gpoch{x}{a}{i}{e}
$$
and $a_m \ne 0$.
Returns 0 if $p = 0$.}
#endif
		polynomial: List POCH -> %;
#if ASDOC
\aspage{polynomial}
\Usage{\name~$[m_0,m_1,\dots,m_n]$}
\Signature{List GeneralizedPochammerMonomial R}{\%}
\Params{ $m_i$ & GeneralizedPochammerMonomial R & Pochammer monomials \\ }
\Retval{Returns $p = \sum_{i=0}^n m_i$.}
\Remarks{
The monomials $m_0,\dots,m_n$ must satisfy the following conditions,
where $m_i = c_i \gpoch{x}{a_i}{d_i}{e_i}$:
\begin{itemize}
\item
$\quad a_0 = a_1 = \dots = a_n$,
\item
$\quad e_0 = e_1 = \dots = e_n$,
\item
$\quad d_0 < d_1 < \dots < d_n$.
\end{itemize}
}
#endif
		if R has RationalRootRing then rationalRoots: % -> List RR;
#if ASDOC
\aspage{rationalRoots}
\Usage{ \name~p }
\Signature{\%}{List RationalRoot}
\Params{ {\em p} & P & A polynomial\\ }
\Retval{Return $[(r_1,e_1),\dots,(r_n,e_n)]$ where the $r_i$'s are
the rational roots of $p$ and have multiplicity $e_i$.}
#endif
		shift: % -> Z;
		shift: (%, Z) -> %;
		shift!: (%, Z) -> %;
#if ASDOC
\aspage{shift}
\Usage{ \name~p \\ \name(p, k) \\ \name!(p, k) }
\Signatures{
\name: & \% $\to$ Integer\\
\name: & (\%, Integer) $\to$ \%\\
\name!: & (\%, Integer) $\to$ \%\\
}
\Params{
{\em p} & \% & A polynomial\\
{\em k} & Integer & The amount of shift\\
}
\Retval{
\name~p returns the common shift of all the monomials of $p$, \ie $e$ where
$$
p = \sum_{i=0}^n a_i \gpoch{x}{a}{i}{e}\;.
$$
\name(p, k) and \name!(p, k) both return p shifted the $k e$ times, \ie
$$
E^{ke} p = \sum_{i=0}^n a_i \gpoch{x}{a+k}{i}{e}
$$
where
$$
p = \sum_{i=0}^n a_i \gpoch{x}{a}{i}{e}
$$
and \name!(p, k) is allowed to destroy or reuse the storage used by p,
so p is lost after that call.}
\Remarks{This function may cause p to be destroyed, so do not use it unless
p has been locally allocated, and is guaranteed not to share space
with other elements. Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
#endif
		start: % -> Z;
#if ASDOC
\aspage{start}
\Usage{\name~p}
\Signature{\%}{Integer}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns the common offset of all the monomials of $p$, \ie $a$ where
$$
p = \sum_{i=0}^n a_i \gpoch{x}{a}{i}{e}\;.
$$
Returns 0 if $p = 0$.}
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
\Usage{\name~p}
\Signature{\%}{Boolean}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns \true~if $p = 0$, \false~otherwise.}
#endif
} == add {
	macro Rep == List POCH;		-- sorted, highest degree term first
					-- all shifts and starts are the same

	import from Z, POCH, Rep;

	0:%				== per empty();
	zero?(p:%):Boolean		== empty? rep p;
	sample:%			== 0;
	(e1:%) = (e2:%):Boolean		== rep e1 = rep e2;
	extree(p:%):TREE		== p extreeSymbol avar;
	shift(p:%, k:Z):%		== per [shift(m, k) for m in rep p];
	shift(p:%):Z			== { zero? p => -1; shift first rep p; }
	start(p:%):Z			== { zero? p => 0; start first rep p; }
	degree(p:%):Z			== { zero? p => 0; degree first rep p; }
	(port:TEXT) << (p:%):TEXT	== port(p, avar);
	generator(p:%):Generator POCH	== generator rep p;
	-(p:%):%			== per [-m for m in rep p];
	(c:R) * (p:%):%			== per [c * m for m in rep p];
	shift!(p:%, k:Z):%	== { for t in rep p repeat shift!(t, k); p; }

	-- uses Horner's rule (sparse)
	-- c0 x^{a,0,e} + c1 x^{a,1,e} + ... + cd x^{a,d,e} =
	-- c0 + (x + ae) (c1 + (x + (a+1)e) (c2 + (x + (a+2)e) (c3 + ... (cd))))
	apply(p:%, x:R):R == {
		zero? p => 0;
		l := rep p;
		v := coefficient first l;		-- cd
		e := shift(p)::R;
		d := degree first l;
		r := x + (start(p) + prev d) * e;	-- x + (a + (d-1)) e
		for m in rest l repeat {
			dm := degree m;
			for i in next dm .. prev d repeat {
				v := r * v;
				r := r - e;
			}
			v := r * v + coefficient m;
			r := r - e;
			d := dm;
		}
		for i in 1..d repeat {
			v := r * v;
			r := r - e;
		}
		v;
	}

	apply(p:%, x:TREE):TREE == {
		import from R, List TREE;
		zero? p => extree(0@R);
		m := first(lm := rep p);
		a := start m;
		e := shift m;
		l := [extree(coefficient m, a, degree m, e, x)];
		for mm in rest lm repeat
			l := cons(extree(coefficient mm, a, degree mm, e, x),l);
		empty? rest l => first l;
		ExpressionTreePlus l;
	}

	local extree(c:R, a:Z, d:Z, e:Z, x:TREE):TREE == {
		import from List TREE;
		negative?(tc := extree c) =>
			ExpressionTreeMinus [extree(c~=-1, negate tc,a,d,e,x)];
		extree(c ~= 1, tc, a, d, e, x);
	}

	local extree(tims?: Boolean, c:TREE, a:Z, d:Z, e:Z, x:TREE):TREE == {
		import from List TREE;
		zero? d => c;
		t := ExpressionTreeGeneralizedPochammer(
					[x, extree a, extree d, extree e]);
		tims? => ExpressionTreeTimes [c, t];
		t;
	}

	apply(port:TEXT, p:%, v:Symbol):TEXT == {
		import from ExpressionTree;
		tex(port, p extreeSymbol v);
	}

	lowestTerm(p:%):POCH == {
		import from R;
		empty?(l := rep p) => monomial(0, 0, 0, -1);
		while ~empty?(rest l) repeat l := rest l;
		first l;
	}

	polynomial(l:List POCH):% == {
		nonzero := [m for m in l | ~zero? m];
		ASSERT ok? nonzero;
		per reverse! nonzero;
	}

	valuesUp(p:%, n:R):Generator R == {
		import from POCH, List Generator R;
		values [valuesUp(m, n) for m in p];
	}

	valuesDown(p:%, n:R):Generator R == {
		import from POCH, List Generator R;
		values [valuesDown(m, n) for m in p];
	}

	local values(l:List Generator R):Generator R == generate {
		repeat {
			s:R := 0;
			for g in l repeat {
				s := add!(s, value g);
				step! g;
			}
			yield s;
		}
	}

	-- a list is ok if all the shifts and starts are equal and
	-- if it is sorted in increasing degree
	local ok?(l:List POCH):Boolean == {
		empty? l => true;
		a := start first l;
		d := degree first l;
		e := shift first l;
		for m in rest l repeat {
			dm := degree m;
			start m ~= a or shift m ~= e or dm <= d => return false;
			d := dm;
		}
		true;
	}

	normalize(p:%):% == {
		zero? p => 0;
		zero?(d := degree(m := lowestTerm p)) => p;
		e := shift m;
		a := start m;
		per [monomial(coefficient t,a+d,degree t - d,e) for t in rep p];
	}

	expand(p:%, P:UnivariatePolynomialCategory R):P == {
		import from R;
		zero? p => 0;
		l := reverse rep p;
		d := degree(m := first l);
		e := shift m;
		a := start m;
		h := pochammer(a, d, e, P);		-- x^{a,d,e}
		c := coefficient m;
		ASSERT(~zero? c);
		q := { one? c => copy h; c * h }	-- always makes a copy
		for t in rest l repeat {
			dm := degree t;
			-- x^{a,dm,e} = x^{a,d,e} x^{a+d,dm-d,e}
			h := times!(h, pochammer(a + d, dm - d, e, P));
			d := dm;
			q := add!(q, coefficient t, h);
		}
		q;
	}

	if R has RationalRootRing then {
		local find(n:Z, l:List RR):Partial RR == {
			import from RR;
			for rt in l | integer? rt repeat
				n = integerValue rt => return [rt];
			failed;
		}

		integerRoots(p:%):List RR == {
			import from Rx;
			ASSERT(~zero? p);
			TRACE("upoch::integerRoots ", p);
			q := expand(normalize p, Rx);
			TRACE("upoch::integerRoots, q = ", q);
			merge(integerRoots q, integerRoots lowestTerm p);
		}

		rationalRoots(p:%):List RR == {
			import from Rx;
			ASSERT(~zero? p);
			q := expand(normalize p, Rx);
			merge(rationalRoots q, integerRoots lowestTerm p);
		}

		local merge(l:List RR, lt:List Z):List RR == {
			import from Z, RR, Partial RR;
			TRACE("upoch::merge, l = ", l);
			TRACE("upoch::merge, lt = ", lt);
			for n in lt repeat {
				u := find(n, l);
				if failed? u then l := cons(integerRoot(n,1),l);
				else {
					r := retract u;
					setMultiplicity!(r,next multiplicity r);
				}
			}
			l;
		}
	}
}
