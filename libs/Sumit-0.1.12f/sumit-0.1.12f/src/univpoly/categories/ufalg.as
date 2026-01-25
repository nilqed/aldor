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
----------------------------- ufalg.as ----------------------------------
#include "sumit"

macro Z == Integer;

#if ASDOC
\thistype{UnivariateFreeAlgebraCategory}
\History{Manuel Bronstein}{22/5/95}{created}
\History{Thom Mulders}{27/5/97}{added partial add!}
\Usage{\this~R: Category}
\Params{ {\em R} & SumitRing & The coefficient ring\\ }
\Descr{\this~is a common category for commutative and noncommutative
univariate polynomials with coefficients in an arbitrary ring R.}
\begin{exports}
\category{Conditional}\\
\category{SumitRing}\\
$\ast$: & (R, \%) $\to$ \% & Left-multiplication by a scalar\\
add!: & (\%, R, \%) $\to$ \% & In-place product and sum\\
add!: & (\%, R, Z) $\to$ \% & In-place addition of a monomial\\
add!: & (\%, R, Z, \%, Z, Z) $\to$ \% & In-place partial product and sum\\
apply: & (R $\to$ R, \%) $\to$ \% & Applies a function to the coefficients\\
apply: & (\%, TREE) $\to$ TREE & Applies a polynomial to a tree\\
apply: & (OUT, \%, String) $\to$ OUT & Write a polynomial to a port\\
apply!: & (R $\to$ R, \%) $\to$ \% & Applies a function to the coefficients\\
coefficient: & (\%, Z) $\to$ R & Extraction of a coefficient\\
coefficients: & \% $\to$ List R & Extraction of all the coefficients\\
coerce: & R $\to$ \% & The natural embedding\\
compose: & (\%, \%) $\to$ \% & Compose polynomials\\
degree: & \% $\to$ Z & The degree of a polynomial\\
generator: & \% $\to$ Generator MON & Make an iterator\\
leadingCoefficient: & \% $\to$ R & The leading coefficient\\
leadingMonomial: & \% $\to$ (R, Z) & The leading term\\
monom: & $\to$ \% & Monomial of degree 1 and coefficient 1\\
monomial: & (R, Z) $\to$ \% & Creation of a single monomial\\
monomial!: & (\%, R, Z) $\to$ \% & In-place monomial\\
momonial?: & \% $\to$ Boolean & Test for a monomial\\
random: & (Z, Z) $\to$ \% & Creation of a random polynomial\\
reductum: & \% $\to$ \% & All terms expect the leading one\\
reverse: & \% $\to$ Generator MON & Make a reverse generator\\
revert: & \% $\to$ \% & Left--Right reversion\\
setCoefficient!: & (\%, Z, R) $\to$ \% &
In-place replacement of a coefficient\\
times!: & (R, \%) $\to$ \% & In-place product by a scalar\\
times: & (\%, \%, Z, Z) $\to$ \% & Partial product\\
trailingMonomial: & \% $\to$ (R, Z) & The lowest term\\
\end{exports}
\begin{aswhere}
MON &==& Cross(R, Z)\\
OUT &==& TextWriter\\
TREE &==& ExpressionTree\\
Z &==& Integer\\
\end{aswhere}
\begin{exports}[if $R$ has CharacteristicZero then]
\category{CharacteristicZero}\\
\end{exports}
\begin{exports}[if $R$ has Field then]
monic: & \% $\to$ \% & Make monic\\
monic!: & \% $\to$ \% & Make monic\\
\end{exports}
\begin{exports}[if $R$ has FiniteCharacteristic then]
\category{FiniteCharacteristic}\\
\end{exports}
\begin{exports}[if R has GcdDomain then]
content: & \% $\to$ R & Polynomial content\\
primitive: & \% $\to$ (R, \%) & Content and primitive part\\
primitivePart: & \% $\to$ \% & Primitive part\\
\end{exports}
\begin{exports}[if $R$ has QRing then]
\category{QRing}\\
\end{exports}
#endif

macro Symbol == String;

UnivariateFreeAlgebraCategory(R:SumitRing):Category ==
	Join(Conditional, SumitRing) with {
	if R has CharacteristicZero then CharacteristicZero;
	if R has FiniteCharacteristic then FiniteCharacteristic;
	if R has QRing then QRing;
	*       : (R, %) -> %;
#if ASDOC
\aspage{$\ast$}
\Usage{c~\name~p}
\Signature{(R, \%)}{\%}
\Params{
{\em c} & R & A scalar\\
{\em p} & \% & A polynomial\\
}
\Retval{Returns the product
$$
c\; p = \sum_{i=0}^n c\; a_i x^i
$$
where $p = \sum_{i=0}^n a_i x^i$.}
\seealso{times!(\this)}
#endif
	add!: (%, R, %) -> %;
	add!: (%, R, Z) -> %;
	add!: (%, R, Z, %) -> %;
	add!: (%, R, Z, %, Z, Z) -> %;
#if ASDOC
\aspage{add!}
\Usage{\name(p, c, q)\\ \name(p, c, m)\\
\name(p, c, m, q)\\ \name(p, c, m, q, n, N)}
\Signatures{
\name: & (\%, R, \%) $\to$ \% \\
\name: & (\%, R, Integer) $\to$ \% \\
\name: & (\%, R, Integer, \%) $\to$ \% \\
\name: & (\%, R, Integer, \%, Integer, Integer) $\to$ \% \\
}
\Params{
{\em p} & \% & A polynomial (to be destroyed)\\
{\em c} & R & A scalar\\
{\em m} & Integer & The degree of the monomial to add\\
{\em q} & \% & A polynomial to be multiplied by $c x^m$ and added to p\\
{\em n} & Integer & A lower threshold\\
{\em N} & Integer & An upper treshold\\
}
\Retval{\name(p, c, m) returns $p + c\; x^m$,
while \name(p, c, q) returns the sum
$$
p + c\; q = \sum_{i=0}^n (a_i + c\; b_i) x^i\,,
$$
\name(p, c, m, q) computes the sum
$$
p + c\; x^m q = \sum_{i=0}^{n+m} (a_i + c\; b_{i-m}) x^i\,,
$$
and \name(p, c, m, q, n, N) computes all the terms of degree at least $n$
and at most $N$ of the above sum,
where $p = \sum_{i=0}^n a_i x^i$ and $q = \sum_{i=0}^n b_i x^i$.
For efficiency reasons it is sometimes sufficient to compute some terms of
that sum only. All other coefficients of $p$ are not changed.}
\Remarks{The storage used by p is allowed to be destroyed or reused, so p
is lost after this call. This may cause p to be destroyed, so do not use
this unless p has been locally allocated, and is thus guaranteed not
to share space with other polynomials. Some functions, like reductum(\this) are
not necessarily copying their arguments and can thus create memory aliases.}
\seealso{+(\this), times!(\this)}
#endif
	apply: (R -> R, %) -> %;
	apply!: (R -> R, %) -> %;
	apply: (%, ExpressionTree) -> ExpressionTree;
	apply: (TextWriter, %, Symbol) -> TextWriter;
#if ASDOC
\aspage{apply}
\Usage{ \name(f, p)\\f~p\\ \name!(f, p)\\ \name(p, t)\\p~t\\
\name(port, p, x)\\ port(p, x) }
\Signatures{
\name: & (R $\to$ R, \%) $\to$ \%\\
\name!: & (R $\to$ R, \%) $\to$ \%\\
\name: & (\%, ExpressionTree) $\to$ ExpressionTree\\
\name: & (TextWriter, \%, String) $\to$ TextWriter\\
}
\Params{
{\em f} & R $\to$ R & A function on $R$\\
{\em p} & \% & A polynomial\\
{\em t} & ExpressionTree & An expression tree\\
{\em port} & TextWriter & An output port\\
{\em x} & String & A name for the variable\\
}
\Descr{
\name(f, p) and \name!(f, p) both return
$$
f(p) = \sum_{i=0}^n f(a_i) x^i
$$
where $p = \sum_{i=0}^n a_i x^i$, $p$ remains unchanged if \name is used,
while the storage used by $p$ is allowed to be destroyed or reused
if \name! is used.\\
\name(p, t) returns the result of evaluating $p$ on the expression tree $t$.\\
\name(port, p, x) sends p to port using x as the variable name,
and returns the output port afterwards.
}
\begin{asex}
\begin{ttyout}
import from Integer, SparseUnivariatePolynomial Integer;

p := monomial(1, 3) + monomial(2, 1) - monomial(1, 0);  -- p = x^3 + 2 x - 1
print(apply((n:Integer):Integer +-> n + n, p), "x");
\end{ttyout}
writes
\Asoutput{ \> 2 x\^\{3\} + 4 x - 2 }
to the standard stream print.
\end{asex}
#endif
	coefficient: (%, Z) -> R;
#if ASDOC
\aspage{coefficient}
\Usage{\name(p, n)}
\Signature{(\%, Integer)}{R}
\Params{
{\em p} & \% & A polynomial\\
{\em n} & Integer & An exponent\\
}
\Retval{Returns the coefficient of the term of degree $n$ in $p$, 0 if there is
no such term.}
\seealso{coefficients(\this),\\ leadingCoefficient(\this) \\
setCoefficient(\this)}
#endif
	coefficients: % -> List R;
#if ASDOC
\aspage{coefficients}
\Usage{\name~p}
\Signature{\%}{List R}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns the list of all the nonzero coefficients of $p$,
sorted by decreasing degree.}
\seealso{coefficient(\this),\\ leadingCoefficient(\this)}
#endif
	coerce:	R -> %;
#if ASDOC
\aspage{coerce}
\Usage{ \name~c\\ c::\% }
\Signature{R}{\%}
\Params{ {\em c} & R & A scalar\\ }
\Descr{Converts $c$ to a polynomial of degree 0 and returns the result.}
#endif
	compose: (%, %) -> %;
#if ASDOC
\aspage{compose}
\Usage{\name(p, q)}
\Params{ {\em p, q} & \% & Polynomials\\ }
\Retval{Returns
$$
p(q) = \sum_{i=0}^n a_i q^i
$$
where $p = \sum_{i=0}^n a_i x^i$.}
#endif
        if R has GcdDomain then {
                content: % -> R;
#if ASDOC
\aspage{content}
\Usage{\name~p}
\Signature{\%}{R}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns
$$
\gcd(a_0,\dots,a_n)
$$
where $p = \sum_{i=0}^n a_i x^i$.}
\seealso{primitive(\this), primitivePart(\this)}
#endif
}
	degree: % -> Z;
#if ASDOC
\aspage{degree}
\Usage{\name~p}
\Signature{\%}{Integer}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns the degree of $p$, \ie $n$ where 
$p = \sum_{i=0}^n a_i x^i$ and $a_n \ne 0$. Returns $-1$ if $p = 0$.}
\seealso{leadingCoefficient(\this),\\ leadingMonomial(\this),
\\ trailingMonomial(\this)}
#endif
	generator: % -> Generator Cross(R, Z);
	reverse: % -> Generator Cross(R, Z);
#if ASDOC
\aspage{generator}
\Usage{
for term in p repeat \{ (c, n) := term; \dots \}\\
for term in \name~p repeat \{ (c, n) := term; \dots \}\\
for term in reverse~p repeat \{ (c, n) := term; \dots \}\\
}
\Signature{\%}{Generator Cross(R, Integer)}
\Params{ {\em p} & \% & A polynomial\\ }
\Descr{Those functions allow a polynomial to be iterated independently of its
representation. Both generators yield pairs of the form $(a, n)$,
with $a \ne 0$ and decreasing (resp.~increasing) exponents for
the function \name (resp.~reverse).}
\begin{asex}
\begin{ttyout}
import from Integer, SparseUnivariatePolynomial(Integer, "x");

p := monomial(1, 3) + monomial(2, 1) - monomial(1, 0);  -- p = x^3 + 2 x - 1;
for term in p repeat { (c, n) := term; print << c << "," << n << newline }
for term in reverse p repeat {(c,n) := term; print << c << "," << n << newline}
\end{ttyout}
writes
\Asoutput{
\> 1,3\\
\> 2,1\\
\> -1,0\\
\> -1,0\\
\> 2,1\\
\> 1,3
}
to the standard stream print.
\end{asex}
\seealso{revert(\this)}
#endif
	leadingCoefficient: % -> R;
#if ASDOC
\aspage{leadingCoefficient}
\Usage{\name~p}
\Signature{\%}{R}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns the leading coefficient of $p$, \ie $a_n$ where
$p = \sum_{i=0}^n a_i x^i$ and $a_n \ne 0$. Returns 0 if $p = 0$.}
\seealso{coefficients(\this), degree(\this),\\ leadingMonomial(\this)}
#endif
	leadingMonomial: % -> (R, Z);
#if ASDOC
\aspage{leadingMonomial}
\Usage{\name~p}
\Signature{\%}{(R, Integer)}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns $(a_n, n)$ where $p = \sum_{i=0}^n a_i x^i$ and $a_n \ne 0$.
Returns $(0, -1)$ if $p = 0$.}
\seealso{degree(\this),\\ leadingCoefficient(\this),
\\ trailingMonomial(\this)}
#endif
	if R has Field then {
		monic: % -> %;
		monic!: % -> %;
#if ASDOC
\aspage{monic}
\Usage{\name~p\\ \name!~p}
\Signature{\%}{\%}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns $a^{-1} p$ where $a$ is the leading coefficient of $p$,
returns $0$ if $p = 0$.}
\Remarks{The storage used by $p$ is allowed to be destroyed or reused
if \name! is used, so $p$ is lost after this call.
This may cause $p$ to be destroyed, so do not use this unless
$p$ has been locally allocated, and is guaranteed not to share space
with other elements. Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
#endif
	}
	monom: %;
#if ASDOC
\aspage{monom}
\Usage{\name}
\Signature{}{\%}
\Retval{Returns $x$, \ie~the monomial with degree 1 and coefficient 1.}
\seealso{monomial(\this)}
#endif
	monomial: (R, Z) -> %;
#if ASDOC
\aspage{monomial}
\Usage{\name(c, n)}
\Signature{(R, Integer)}{\%}
\Params{
{\em c} & R & A scalar\\
{\em n} & Integer & An exponent\\
}
\Retval{Returns the polynomial $c\; x^n$.}
\seealso{monom(\this), monomial!(\this)}
#endif
	monomial!: (%, R, Z) -> %;
#if ASDOC
\aspage{monomial!}
\Usage{\name(p, c, n)}
\Signature{(\%, R, Integer)}{\%}
\Params{
{\em p} & \% & A polynomial (to be destroyed)\\
{\em c} & R & A scalar\\
{\em n} & Integer & An exponent\\
}
\Retval{Returns the polynomial $c\; x^n$,
where the storage used by $p$ is allowed to be destroyed or reused.}
\Remarks{The storage used by $p$ is allowed to be destroyed or reused,
so $p$ is lost after this call.
This may cause $p$ to be destroyed, so do not use this unless
$p$ has been locally allocated, and is guaranteed not to share space
with other elements. Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
\seealso{monomial(\this)}
#endif
	monomial?: % -> Boolean;
#if ASDOC
\aspage{monomial?}
\Usage{\name~p}
\Signature{\%}{Boolean}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns \true~if $p = a x^n$ for $a \in R$, \false~otherwise.}
\Remarks{\name(0) returns \true.}
#endif
        if R has GcdDomain then {
                primitive: % -> (R, %);
#if ASDOC
\aspage{primitive}
\Usage{\name~p}
\Signature{\%}{(R, \%)}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns
$$
(c, c^{-1} p)
$$
where $c = \mbox{content}(p)$.}
\seealso{content(\this), primitivePart(\this)}
#endif
                primitivePart: % -> %;
#if ASDOC
\aspage{primitivePart}
\Usage{\name~p}
\Signature{\%}{\%}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns
$$
\mbox{content}(p)^{-1} p\,.
$$
}
\seealso{content(\this), primitive(\this)}
#endif
}
	random: (Z, m:Z == -1) -> %;
#if ASDOC
\aspage{random}
\Usage{\name(n[, m])}
\Signature{(Integer, Integer)}{\%}
\Params{
{\em n} & Integer & The desired degree\\
{\em m} & Integer & The desired number of terms (optional)\\
}
\Retval{Returns a monic random polynomial of degree $n$ with at most $m$ terms,
($n+1$ terms if $m$ is not present).}
#endif
	reductum: % -> %;
#if ASDOC
\aspage{reductum}
\Usage{\name~p}
\Signature{\%}{\%}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns the reductum of $p$, \ie $\sum_{i=0}^{n-1} a_i x^i$ where
$p = \sum_{i=0}^n a_i x^i$ and $a_n \ne 0$. Returns 0 if $p = 0$.}
#endif
	revert: % -> %;
#if ASDOC
\aspage{revert}
\Usage{\name~p}
\Signature{\%}{\%}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns
$\sum_{i=0}^n a_i x^{n-i}$
where
$p = \sum_{i=0}^n a_i x^i$ and $a_n \ne 0$. Returns 0 if $p = 0$.}
\seealso{reverse(\this)}
#endif
	setCoefficient!: (%, Z, R) -> %;
#if ASDOC
\aspage{setCoefficient!}
\Usage{\name(p, n, c)}
\Signature{(\%,Integer,R)}{\%}
\Params{
{\em p} & \% & A polynomial\\
{\em n} & Integer & An exponent\\
{\em c} & R & A coefficient\\
}
\Descr{Sets the coefficient of $x^n$ in $p$ to $c$,
and returns the modified $p$.}
\Remarks{The storage used by p is allowed to be destroyed or reused, so p
is lost after this call.
This may cause p to be destroyed, so do not use this unless
p has been locally allocated, and is thus guaranteed not to share space
with other polynomials. Some functions, like reductum(\this) are
not necessarily copying their arguments and can thus create memory aliases.}
\seealso{coefficient(\this)}
#endif
	times!: (R, %) -> %;
#if ASDOC
\aspage{times!}
\Usage{\name(c, p)}
\Signature{(R, \%)}{\%}
\Params{
{\em c} & R & A scalar to be multiplied by p\\
{\em p} & \% & A polynomial (to be destroyed)\\
}
\Retval{\name(c, p) returns the product
$$
c\; p = \sum_{i=0}^n c\; a_i x^i
$$
where $p = \sum_{i=0}^n a_i x^i$.}
\Remarks{The storage used by p is allowed to be destroyed or reused, so p
is lost after this call.
This may cause p to be destroyed, so do not use this unless
p has been locally allocated, and is thus guaranteed not to share space
with other polynomials. Some functions, like reductum(\this) are
not necessarily copying their arguments and can thus create memory aliases.}
\seealso{$\ast$(\this), add!(\this)}
#endif
	times: (%, %, Z, Z) -> %;
#if ASDOC
\aspage{times}
\Usage{\name(p, q, l, h)}
\Signature{(\%, \%, Integer, Integer)}{\%}
\Params{
{\em p, q} & \% & Polynomials\\
{\em l, h} & Integer & Lower and upper bound of coefficients to be computed
}
\Retval{\name(p, q, l, h) returns a polynomial $s$ containing some coefficients
of the product $pq$. The $i$th coefficient of $s$ equals the $l+i$th coefficient
of $pq$. Here $l\le h$ should hold.}
\seealso{$\ast$(\this)}
#endif

	trailingMonomial: % -> (R, Z);
#if ASDOC
\aspage{trailingMonomial}
\Usage{\name~p}
\Signature{\%}{(R, Integer)}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns $(a_m, m)$ where $p = \sum_{i=m}^n a_i x^i$ and $a_m \ne 0$.
Returns $(0, -1)$ if $p = 0$.}
\seealso{degree(\this),\\ leadingCoefficient(\this),\\ leadingMonomial(\this)}
#endif
	default {
		test(p:%):Boolean		== not zero? p;
		add!(p:%, c:R, q:%):%		== add!(p, c * q);
		add!(p:%, c:R, n:Z):%		== add!(p, monomial(c, n));
		times!(c:R, p:%):%		== c * p;
		characteristic:Z		== characteristic$R;
		coerce(n:Z):%			== n::R::%;
		coerce(n:SingleInteger):%	== n::R::%;
		apply!(f:R -> R, p:%):%		== apply(f, p);
		monomial!(p:%, c:R, n:Z):%	== monomial(c, n);
		monomial?(p:%):Boolean		== zero? reductum p;
		coerce(c:R):%		== { import from Z; monomial(c, 0); }
		monom:%			== { import from R, Z; monomial(1, 1); }
		sample:%			== monom;
		leadingMonomial(p:%):(R, Z) == (leadingCoefficient p, degree p);

		add!(p:%, c:R, n:Z, q:%):% ==
			add!(p, c, n, q, 0, max(degree p, degree q + n));

		-- TEMPORARY: WANT for (c, n) in p  (BUG970)
		local bugworkaround(c:R, n:Z):R == c;
		coefficients(p:%):List R == [bugworkaround term for term in p];

		copy(p:%):% == {
			q:% := 0;
			for term in p repeat {
				(c, n) := term;
				q := add!(q, c, n);
			}
			q;
		}

		apply(port:TextWriter, p:%, v:Symbol):TextWriter == {
			import from ExpressionTree;
			tex(port, p extreeSymbol v);
		}

		apply(p:%, x:ExpressionTree):ExpressionTree == {
			import from List ExpressionTree;
			zero? p => extree(0@R);
			l:List(ExpressionTree) := empty();
			for term in p repeat {
				(c, n) := term;
				l := cons(extree(c, n, x), l);
			}
			ASSERT(~empty? l);
			empty? rest l => first l;
			ExpressionTreePlus reverse! l;
		}

		local extree(c:R, d:Z, t:ExpressionTree):ExpressionTree == {
			import from List ExpressionTree;
			negative?(tc := extree c) =>
			   ExpressionTreeMinus [extree(c~=-1, negate tc, d, t)];
			extree(c ~= 1, tc, d, t);
		}

		local extree(tims?:Boolean, c:ExpressionTree, n:Z,
			t:ExpressionTree):ExpressionTree == {
				import from R, List ExpressionTree;
				zero? n => c;
				if n > 1 then
					t := ExpressionTreeExpt [t, extree n];
				tims? => ExpressionTreeTimes [c, t];
				t;
		}

		apply(f:R -> R, p:%):% == {
			q:% := 0;
			for term in p repeat {
				(c, n) := term;
				q := add!(q, f c, n);
			}
			q;
		}

		times(a:%, b:%, l:Z, h:Z):% == {
			p := a * b;
			s:% := 0;
			for i in l..min(degree p, h) repeat
				s := add!(s, coefficient(p, i), i - l);
			s
		}

		-- TEMPORARY: SEG FAULT IF FUNCTION IS NOT LOCAL (928)
		-- TEMPORARY: local KEYWORD REQUIRED (965)
		local prod(a:%, b:%):% == times!(a, b);
		(p:%) ^ (n:Z):% == {
			ASSERT(n >= 0);
			import from BinaryPowering(%, prod, Z);
			zero? n => 1; one? n => p;
			power(1, copy p, n);
		}

		compose(p:%, q:%):% == {
			import from Z;
			q = monom => p;
			pq:% := 0;
			zero? q => pq;
			qn:% := 1;
			d:Z := 0;
			for term in reverse p repeat {
				(c, n) := term;
				for i in 1..n - d repeat
					zero?(qn := q * qn) => return pq;
				pq := add!(pq, c * qn);
				d := n;
			}
			pq;
		}

		random():% == {
			import from RandomNumberGenerator;
			d := randomInteger() rem 101;
			random(d, (3 * d) quo 4);
		}

		random(n:Z, m:Z):% == {
			import from RandomNumberGenerator;
			ASSERT(n >= 0);
			if m < 0 or m > n+1 then m := n+1;
			p := monomial(1, n) + monomial(random(), 0);
			gen := randomGenerator(0, 1, n-1);
			for i in 3..m repeat p := add!(p, random(), gen());
			p;
		}

		revert(p:%):% == {
			zero? p => p;
			d := degree p;
			q:% := 0;
			-- reverse is important so that the high degree terms
			-- are created first (space-efficiency)
			for term in reverse p repeat {
				(c, e) := term;
				q := add!(q, c, d - e);
			}
			q;
		}

		if R has QRing then
			inv(n:Z):% == { import from R; inv(n)$R :: % };

		if R has GcdDomain then {
			-- TEMPORARY: WANT REDEFINITION IF R HAS FIELD
			local field?:Boolean := R has Field;

			primitivePart(p:%):% == {
				field? => p;
				(c, q) := primitive p;
				q;
			}

			content(p:%):R == {
				import from R;
				field? => 1;
				gcd coefficients p;
			}

			primitive(p:%):(R, %) == {
				import from R, Partial R;
				field? => (1, p);
				c := content p;
				(c,
				 apply((r:R):R+->retract exactQuotient(r,c),p));
			}
		}

		if R has Field then {
			monic(p:%):% == {
				import from R;
				zero? p or one?(a := leadingCoefficient p) => p;
				inv(a) * p;
			}

			monic!(p:%):% == {
				import from R;
				zero? p or one?(a := leadingCoefficient p) => p;
				times!(inv a, p);
			}
		}
	}
}
