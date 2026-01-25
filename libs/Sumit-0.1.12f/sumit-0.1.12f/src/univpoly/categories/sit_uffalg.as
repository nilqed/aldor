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
----------------------------- sit_uffalg.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"

macro {
	Z == Integer;
	RR == (R pretend Ring);
}

#if ALDOC
\thistype{UnivariateFreeFiniteAlgebra}
\History{Manuel Bronstein}{22/5/95}{created}
\History{Thom Mulders}{27/5/97}{added partial add!}
\History{Manuel Bronstein}{14/4/2000}{separated the common series/poly exports}
\Usage{\this~R: Category}
\Params{
{\em R} & \astype{SumitType} & The coefficient domain\\
        & \astype{ArithmeticType} &\\
}
\Descr{\this~is a common category for commutative and noncommutative
univariate polynomials with coefficients in an arbitrary arithmetic
system R and with respect to an arbitrary basis $(P_n)_{n \ge 0}$.}
\begin{exports}
\category{\astype{CopyableType}}\\
\category{\astype{UnivariateFreeAlgebra} R}\\
\asexp{coerce}: & \astype{Vector} R $\to$ \% & Create a polynomial\\
\asexp{companion}: & \% $\to$ \astype{DenseMatrix} R & Companion matrix\\
\asexp{degree}: & \% $\to$ Z & The degree of a polynomial\\
\asexp{generator}: & \% $\to$ \astype{Generator} MON & Make an iterator\\
\asexp{leadingCoefficient}: & \% $\to$ R & The leading coefficient\\
\asexp{leadingMonomial}: & \% $\to$ (R, Z) & The leading term\\
\asexp{monomial!}: & (\%, R, Z) $\to$ \% & In-place monomial\\
\asexp{momonial?}: & \% $\to$ Boolean & Test for a monomial\\
\asexp{reductum}: & \% $\to$ \% & All terms except the leading one\\
\asexp{revert}: & \% $\to$ \% & Left--Right reversion\\
\asexp{terms}: & \% $\to$ \astype{Generator} MON & Make an iterator\\
\asexp{times}: & (\%, \%, Z, Z) $\to$ \% & Partial product\\
\asexp{trailingCoefficient}: & \% $\to$ R & The lowest coefficient\\
\asexp{trailingDegree}: & \% $\to$ Z & Degree of the lowest term\\
\asexp{trailingMonomial}: & \% $\to$ (R, Z) & The lowest term\\
\asexp{vectorize!}:
& \astype{Vector} R $\to$ \% $\to$ \astype{Vector} R &
Conversion to a vector\\
\end{exports}
\begin{aswhere}
MON &==& \builtin{Cross}(R, Z)\\
Z &==& \astype{Integer}\\
\end{aswhere}
\begin{exports}[if $R$ has \astype{Field} then]
\asexp{monic}: & \% $\to$ \% & Make monic\\
\asexp{monic!}: & \% $\to$ \% & Make monic\\
\end{exports}
\begin{exports}[if R has \astype{GcdDomain} then]
\asexp{content}: & \% $\to$ R & Polynomial content\\
                 & (\%, \astype{Automorphism} R) $\to$ R & \\
\asexp{primitive}: & \% $\to$ (R, \%) & Content and primitive part\\
                 & (\%, \astype{Automorphism} R) $\to$ (R, \%) & \\
\asexp{primitivePart}: & \% $\to$ \% & Primitive part\\
                 & (\%, \astype{Automorphism} R) $\to$ \% & \\
\end{exports}
\begin{exports}[if $R$ has \astype{CharacteristicZero} then]
\category{\astype{CharacteristicZero}}\\
\end{exports}
\begin{exports}[if $R$ has \astype{FiniteCharacteristic} then]
\category{\astype{FiniteCharacteristic}}\\
\end{exports}
\begin{exports}[if $R$ has \astype{HashType} then]
\category{\astype{HashType}}\\
\end{exports}
\begin{exports}[if $R$ has \astype{QRing} then]
\category{\astype{QRing}}\\
\end{exports}
\begin{exports}[if $R$ has \astype{Ring} then]
\category{\astype{Algebra} R}\\
\asexp{random}: & (\astype{Integer}, \astype{Integer}) $\to$ \% &
Creation of a random polynomial\\
\end{exports}
\begin{exports}[if $R$ has \astype{SerializableType} then]
\category{\astype{SerializableType}}\\
\end{exports}
#endif

define UnivariateFreeFiniteAlgebra(R:Join(ArithmeticType,SumitType)):Category ==
	Join(CopyableType, UnivariateFreeAlgebra R) with {
	if R has CharacteristicZero then CharacteristicZero;
	if R has FiniteCharacteristic then FiniteCharacteristic;
	if R has QRing then QRing;
	if R has SerializableType then SerializableType;
	if R has HashType then HashType;
	coerce: Vector R -> %;
	vectorize!: Vector R -> % -> Vector R;
#if ALDOC
\aspage{coerce,vectorize!}
\astarget{coerce}
\astarget{vectorize!}
\Usage{v::\%\\ vectorize! v\\ vectorize!(v)(p)}
\Signatures{
coerce: & \astype{Vector} R $\to$ \%\\
vectorize!: & \astype{Vector} R $\to$ \% $\to$ \astype{Vector} R\\
}
\Params{
{\em p} & \% & A polynomial\\
{\em v} & \astype{Vector} R & A coefficient vector\\
}
\Descr{$[v_1,\dots,v_n]$::\% returns the polynomial
$\sum_{i=0}^{n-1} v_{i+1} P_i$, while
vectorize!$(v)(\sum_{j=0}^d a_j P_j)$ fills $v$ with $[a_0,\dots,a_d,0,\dots]$
and returns $v$.}
\Remarks{If $d > \#v - 1$, then the high coefficients of $p$ are
simply ignored.}
#endif
	companion: % -> DenseMatrix R;
#if ALDOC
\aspage{companion}
\Usage{\name~p}
\Signature{\%}{\astype{DenseMatrix} R}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns the companion matrix
$$
\pmatrix{
0   &        &   &     &  -a_0    \cr
a_n & \ddots &   &     &  -a_1    \cr
    & \ddots &   &     &  -a_2    \cr
    &        &   &     & \vdots   \cr
    &        &   & a_n &  -a_{n-1}\cr
}
$$
where $p = \sum_{i=0}^n a_i P_i$.}
#endif
        if R has GcdDomain then {
                content: % -> R;
                content: (%, Automorphism RR) -> R;
                primitive: % -> (R, %);
                primitive: (%, Automorphism RR) -> (R, %);
                primitivePart: % -> %;
                primitivePart: (%, Automorphism RR) -> %;
#if ALDOC
\aspage{content,primitive,primitivePart}
\astarget{content}
\astarget{primitive}
\astarget{primitivePart}
\Usage{content~p\\ content(p, $\sigma$)\\
primitive~p\\ primitive(p, $\sigma$)\\
primitivePart~p\\ primitivePart(p, $\sigma$)}
\Signatures{
content: & \% $\to$ R\\
content: & (\%, \astype{Automorphism} R) $\to$ R\\
primitive: & \% $\to$ (R, \%)\\
primitive: & (\%, \astype{Automorphism} R) $\to$ (R, \%)\\
primitivePart: & \% $\to$ \%\\
primitivePart: & (\%, \astype{Automorphism} R) $\to$ \%\\
}
\Params{
{\em p} & \% & A polynomial\\
$\sigma$ & \astype{Automorphism} R & An automorphism of $R$ (optional)\\
}
\Descr{content(p, $\sigma$) returns
$$
\gcd(a_0,\sigma a_1,\dots,\sigma^n a_n)
$$
where $p = \sum_{i=0}^n a_i P_i$,
while primitive(p, $\sigma$) and primitivePart(p, $\sigma$) return respectively
$(c, c^{-1} p)$ and $c^{-1} p$ where $c = \mbox{content}(p, \sigma)$.
The parameter $\sigma$ is optional and is taken to be the identity by default.}
#endif
	}
	degree: % -> Z;
	trailingDegree: % -> Z;
#if ALDOC
\aspage{degree,trailingDegree}
\astarget{degree}
\astarget{trailingDegree}
\Usage{degree~p\\ trailingDegree~p}
\Signature{\%}{\astype{Integer}}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{degree(p) and trailingDegree(p) return respectively the degree
and trailing degree of $p$, \ie $n$ and $m$ where 
$p = \sum_{i=m}^n a_i P_i$ and $a_n \ne 0 \ne a_m$.
Both return $-1$ when $p = 0$.}
\seealso{\asexp{leadingCoefficient},\asexp{leadingMonomial},
\asexp{trailingCoefficient},\asexp{trailingMonomial}}
#endif
	generator: % -> Generator Cross(R, Z);
	terms: % -> Generator Cross(R, Z);
#if ALDOC
\aspage{generator,terms}
\astarget{generator}
\astarget{terms}
\Usage{
for term in p repeat \{ (c, n) := term; \dots \}\\
for term in generator~p repeat \{ (c, n) := term; \dots \}\\
for term in terms~p repeat \{ (c, n) := term; \dots \}\\
}
\Signature{\%}{\astype{Generator} \builtin{Cross}(R, \astype{Integer})}
\Params{ {\em p} & \% & A polynomial\\ }
\Descr{Both functions allow a polynomial to be iterated independently of its
representation. Both generators yield pairs of the form $(a, n)$,
with $a \ne 0$. The difference between the two is that
generator(p) yields the terms in decreasing exponents, while
terms(p) yields the terms in increasing exponents.}
\begin{asex}
\begin{ttyout}
import from Integer, DenseUnivariatePolynomial Integer;

x := monom;
p := x^3 + 2*x - 1;
for term in p repeat { (c, n) := term; print << c << "," << n << newline }
\end{ttyout}
writes
\begin{asoutput}
\> 1,3\\
\> 2,1\\
\> -1,0\\
\end{asoutput}
to the standard stream print.
\end{asex}
\seealso{\asfunc{UnivariateFreeAlgebra}{coefficients}, \asexp{revert}}
#endif
	leadingCoefficient: % -> R;
	trailingCoefficient: % -> R;
#if ALDOC
\aspage{leadingCoefficient,trailingCoefficient}
\aspage{leadingCoefficient}
\aspage{trailingCoefficient}
\Usage{leadingCoefficient~p\\ trailingCoefficient~p}
\Signature{\%}{R}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{leadingCoefficient(p) and trailingCoefficient(p)
return respectively the leading and trailing coefficient of $p$,
\ie $a_n$ and $a_m$ where
$p = \sum_{i=m}^n a_i P_i$ and $a_n \ne 0 \ne a_m$.
Both return 0 when $p = 0$.}
\seealso{\asfunc{UnivariateFreeAlgebra}{coefficients}, \asexp{degree},
\asexp{leadingMonomial}, \asexp{trailingDegree}}
#endif
	leadingMonomial: % -> (R, Z);
	trailingMonomial: % -> (R, Z);
#if ALDOC
\aspage{leadingMonomial,trailingMonomial}
\astarget{leadingMonomial}
\astarget{trailingMonomial}
\Usage{leadingMonomial~p\\ trailingMonomial~p}
\Signature{\%}{(R, \astype{Integer})}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{leadingMonomial(p) and trailingMonomial(p)
return respectively $(a_n, n)$ and $(a_m, m)$
where $p = \sum_{i=m}^n a_i P_i$ and $a_n \ne 0 \ne a_m$.
Both return $(0, -1)$ when $p = 0$.}
\seealso{\asexp{degree},\asexp{leadingCoefficient},
\asexp{trailingCoefficient},\asexp{trailingDegree}}
#endif
	if R has Field then {
		monic: % -> %;
		monic!: % -> %;
#if ALDOC
\aspage{monic}
\astarget{\name!}
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
	monomial!: (%, R, Z) -> %;
#if ALDOC
\aspage{monomial!}
\Usage{\name(p, c, n)}
\Signature{(\%, R, \astype{Integer})}{\%}
\Params{
{\em p} & \% & A polynomial (to be destroyed)\\
{\em c} & R & A scalar\\
{\em n} & \astype{Integer} & An exponent\\
}
\Retval{Returns the monomial $c P_n$.}
\Remarks{The storage used by $p$ is allowed to be destroyed or reused
so $p$ is lost after this call.
This may cause $p$ to be destroyed, so do not use this unless
$p$ has been locally allocated, and is guaranteed not to share space
with other elements. Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
#endif
	monomial?: % -> Boolean;
#if ALDOC
\aspage{monomial?}
\Usage{\name~p}
\Signature{\%}{Boolean}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns \true~if $p = a P_n$ for $a \in R$, \false~otherwise.}
\Remarks{\name(0) returns \true.}
#endif
	if R has Ring then {
		Algebra(R pretend Ring);
		random: (Z, m:Z == -1) -> %;
#if ALDOC
\aspage{random}
\Usage{\name(n[, m])}
\Signature{(\astype{Integer}, \astype{Integer})}{\%}
\Params{
{\em n} & \astype{Integer} & The desired degree\\
{\em m} & \astype{Integer} & The desired number of terms (optional)\\
}
\Retval{Returns a monic random polynomial of degree $n$ with at most $m$ terms,
($n+1$ terms if $m$ is not present).}
#endif
	}
	reductum: % -> %;
#if ALDOC
\aspage{reductum}
\Usage{\name~p}
\Signature{\%}{\%}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns the reductum of $p$, \ie~$\sum_{i=0}^{n-1} a_i P_i$ where
$p = \sum_{i=0}^n a_i P_i$ and $a_n \ne 0$. Returns 0 if $p = 0$.}
#endif
	revert: % -> %;
#if ALDOC
\aspage{revert}
\Usage{\name~p}
\Signature{\%}{\%}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns
$\sum_{i=0}^n a_i P_{n-i}$
where
$p = \sum_{i=0}^n a_i P_i$ and $a_n \ne 0$. Returns 0 if $p = 0$.}
\seealso{\asfunc{UnivariateFreeAlgebra}{terms}}
#endif
	times: (%, %, Z, Z) -> %;
#if ALDOC
\aspage{times}
\Usage{\name(p, q, l, h)}
\Signature{(\%, \%, \astype{Integer}, \astype{Integer})}{\%}
\Params{
{\em p, q} & \% & Polynomials\\
{\em l, h} & \astype{Integer} &
Lower and upper bound of coefficients to be computed\\
}
\Retval{\name(p, q, l, h) returns a polynomial $s$ containing some coefficients
of the product $pq$. The $i$th coefficient of $s$ equals the $l+i$th
coefficient of $pq$. Here $l\le h$ should hold.}
#endif
	default {
		monomial!(p:%,c:R,n:Z):%== monomial(c, n);
		monomial?(p:%):Boolean	== zero? reductum p;

		coefficients(p:%):Generator R == generate {
			import from Z;
			for i in 0..degree p repeat yield coefficient(p, i);
		}

		relativeSize(p:%):MachineInteger == {
			import from Z;
			zero? p => 0;
			machine degree p;
		}

		leadingCoefficient(p:%):R == {
			(c, n) := leadingMonomial p;
			c;
		}

		degree(p:%):Z == {
			(c, n) := leadingMonomial p;
			n;
		}

		trailingCoefficient(p:%):R == {
			(c, n) := trailingMonomial p;
			c;
		}

		trailingDegree(p:%):Z == {
			(c, n) := trailingMonomial p;
			n;
		}

		shift(p:%, n:Z):% == {
			zero? n => p;
			q:% := 0;
			pos? := n > 0;
			for term in p repeat {
				(a, d) := term;
				e := d + n;
				if pos? or e >= 0 then q := add!(q, a, e);
			}
			q;
		}

		companion(p:%):DenseMatrix R == {
			import from MachineInteger, Z, R;
			zero? p or zero?(d := degree p) => zero(0, 0);
			n := machine d;
			v:Vector R := zero(n := machine d);
			for term in p repeat {
				(c, e) := term;
				ee := machine e;
				if ee < n then v(next ee) := -c;
			}
			companion(v, leadingCoefficient p);
		}

		copy(p:%):% == {
			q:% := 0;
			for term in p repeat {
				(c, n) := term;
				q := add!(q, c, n);
			}
			q;
		}

		map(f:R -> R)(p:%):% == {
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

		if R has Ring then {
			coerce(n:Z):% == { import from R; monomial(n::R, 0); }

			-- TEMPORARY: 1.1.12p4 DOES NOT SEE THE Algebra DEFAULT
			characteristic:Z == characteristic$R;

			random():% == {
				import from Z;
				d := random()$Z rem 101;
				random(d, (3 * d) quo 4);
			}

			random(n:Z, m:Z):% == {
				import from R;
				assert(n >= 0);
				if m < 0 or m > n+1 then m := n+1;
				p := monomial(1, n) + monomial(random(), 0);
				for i in 3..m repeat
					p := add!(p,random(),random()@Z rem n);
				p;
			}
		}

		revert(p:%):% == {
			zero? p => p;
			d := degree p;
			q:% := 0;
			-- terms is important so that the high degree terms
			-- are created first (space-efficiency)
			for term in terms p repeat {
				(c, e) := term;		-- low to high
				q := add!(q, c, d - e);
			}
			q;
		}

		vectorize!(v:Vector R): % -> Vector R == {
			import from MachineInteger, Z;
			n := #v;
			(p:%):Vector R +-> {
				for i in 1..n repeat
					v.i := coefficient(p, prev(i)::Z);
				v;
			}
		}

		coerce(v:Vector R):% == {
			import from MachineInteger, Z;
			zero?(n := #v) => 0;
			n1 := prev n;
			p := monomial(v.n, n1::Z);
			for i in n1..1 by -1 repeat p := add!(p,v.i,prev(i)::Z);
			p;
		}

		if R has QRing then
			inv(n:Z):% == { import from R; inv(n)$R :: % };

		if R has Field then {
			-- TEMPORARY: WANT THOSE DEFS EVENTUALLY
			-- content(p:%):R		== 1;
			-- primitivePart(p:%):%	== p;
			-- primitive(p:%):(R, %)	== (1, p);
			-- content(p:%, s:Automorphism R):R		== 1;
			-- primitivePart(p:%, s:Automorphism R):%	== p;
			-- primitive(p:%, s:Automorphism R):(R, %)	==(1,p);

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

		if R has GcdDomain then {
			local field?:Boolean	== R has Field;
			local coef(c:R, n:Z):R	== c;

			content(p:%):R == {
				import from List R;
				field? =>  1;
				gcd [coef term for term in p];
			}

			content(p:%, s:Automorphism RR):R == {
				import from Boolean, R;
				field? => 1;
				g:R := 0;
				for term in p while ~unit? g repeat {
					(c, n) := term;
					g := gcd(g, s(c, n));
				}
				g;
			}

			primitivePart(p:%):% == {
				field? => p;
				(c, q) := primitive p;
				q;
			}

			primitivePart(p:%, s:Automorphism RR):% == {
				field? => p;
				(c, q) := primitive(p, s);
				q;
			}

			primitive(p:%):(R, %) == {
				import from R;
				field? => (1, p);
				one?(c := content p) => (c, p);
				(c, map((r:R):R +-> quotient(r, c)) p);
			}

			primitive(p:%, s:Automorphism RR):(R, %) == {
				import from R;
				field? => (1, p);
				one?(c := content p) => (c, p);
				q:% := 0;
				for term in p repeat {
					(a, n) := term;
					q := add!(q, quotient(s(a, n), c), n);
				}
				(c, q);
			}
		}

		-- default is sparse dumping, terminated by 0 P_{-1}
		if R has SerializableType then {
			(port:BinaryWriter) << (p:%):BinaryWriter == {
				import from R, Z;
				for term in p repeat {
					(c, n) := term;
					port := port << c << n;
				}
				port << 0@R << (-1)@Z;
			}

			<< (port:BinaryReader):% == {
				import from R, Z;
				p:% := 0;
				n:Z := 0;
				local c:R;
				while n >= 0 repeat {
					c := << port;
					n := << port;
					if n >= 0 then p := add!(p, c, n);
				}
				p;
			}
		}

		if R has HashType then {
			hash(p:%):MachineInteger == {
				import from R;
				h:MachineInteger := 0;
				for term in p repeat {
					(c, n) := term;
					h := h + hash(c) + machine n;
				}
				h;
			}
		}
	}
}

#if ALDOC
\thistype{UnivariateFreeFiniteAlgebra2}
\History{Manuel Bronstein}{27/7/2000}{created}
\Usage{import from \this(R,Rx,S,Sy)}
\Params{
{\em R, S} & \astype{SumitType} & Coefficient domains\\
           & \astype{ArithmeticType} &\\
{\em Rx}
& \astype{UnivariateFreeFiniteAlgebra} R & A free finite algebra over $R$\\
{\em Sy}
& \astype{UnivariateFreeFiniteAlgebra} S & A free finite algebra over $R$\\
}
\Descr{\this(R,Rx,S,Sy) provides tools for lifting maps $R \to S$ to
maps $Rx \to Sy$.}
\begin{exports}
\asexp{map}: & (R $\to$ S) $\to$ Rx $\to$ Sy & Lift a mapping\\
\end{exports}
#endif

UnivariateFreeFiniteAlgebra2(R:Join(ArithmeticType, SumitType),
				RX:UnivariateFreeFiniteAlgebra R,
				S:Join(ArithmeticType, SumitType),
				SX:UnivariateFreeFiniteAlgebra S): with {
	map: (R -> S) -> RX -> SX;
#if ALDOC
\aspage{map}
\Usage{\name~f\\\name(f)(p)}
\Signature{(R $\to$ S) $\to$ Rx}{Sy}
\Params{
{\em f} & R $\to$ S & A map\\
{\em p} & \% & A polynomial with coefficient in $R$\\
}
\Descr{\name(f)(p) returns
$$
f(p) = \sum_i f(a_i) y^i
$$
where $p = \sum_i a_i x^i$, while \name(f) returns the mapping $p \to f(p)$.}
#endif
} == add {
	map(f:R -> S)(p:RX):SX == {
		q:SX := 0;
		for term in p repeat {
			(c, n) := term;
			q := add!(q, f c, n);
		}
		q;
	}
}

