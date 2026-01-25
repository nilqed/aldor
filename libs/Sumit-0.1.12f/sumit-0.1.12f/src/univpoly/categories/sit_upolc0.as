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
----------------------------- sit_upolc0.as --------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I == MachineInteger;
	Z == Integer;
	V == Vector;
	M == DenseMatrix;
}

-- The documentation for this type is meant to be included in sit_upolc.tex,
-- since UnivariatePolynomialCategory0 is not documented separately
define UnivariatePolynomialCategory0(R:Join(ArithmeticType, SumitType)):
	Category == UnivariatePolynomialAlgebra R with {
	apply: (%, R) -> R;
	apply: (%, %) -> %;
#if ALDOC
\aspage{apply}
\Usage{ \name(p, a)\\ \name(p, q)\\ p~a\\ p~q }
\Signatures{
\name: & (\%, R) $\to$ R\\
\name: & (\%, \%) $\to$ \%\\
}
\Params{
{\em p} & \% & A polynomial\\
{\em q} & \% & A polynomial\\
{\em a} & R & A scalar\\
}
\Retval{
Returns
$$
p(a) = \sum_{i=0}^n a_i a^i
$$
or
$$
p(q) = \sum_{i=0}^n a_i q^i
$$
where $p = \sum_{i=0}^n a_i x^i$.}
#endif
	equal?: (%, %, %, Z) -> Boolean;
#if ALDOC
\aspage{equal?}
\Usage{\name(a, b, c, n)}
\Signature{(\%, \%, \%, \astype{Integer})}{\astype{Boolean}}
\Params{
{\em a, b, c} & \% & Polynomials \\
{\em n} & \astype{Integer} & The order of truncation\\
}
\Retval{Returns \true~if $a = b c \pmod{x^n}$, \false~otherwise.}
#endif
	if R has OrderedArithmeticType then height: % -> R;
#if ALDOC
\aspage{height}
\Usage{\name~p}
\Signature{\%}{R}
\Params{ {\em p} & \% & A polynomial\\ }
\Retval{Returns
$$
\vert\vert p \vert\vert_\infty = \max_{i=0}^n\left(\vert a_i \vert\right)
$$
where $p = \sum_{i=0}^n a_i x^i$.}
#endif
	Horner: (%, R) -> (%, R);
#if ALDOC
\aspage{Horner}
\Usage{\name(p, a)}
\Signature{(\%, R)}{(\%, R)}
\Params{
{\em p} & \% & A polynomial\\
{\em a} & R & A point\\
}
\Retval{Returns $(q, p(a))$ such that $p = q (x - a) + p(a)$.}
#endif
	if R has CommutativeRing then {
		DifferentialRing;
		if R has QRing then {
			integrate: % -> %;
			integrate: (%, Integer) -> %;
		}
#if ALDOC
\aspage{integrate}
\Usage{\name~p\\ \name(p, n)}
\Signatures{
\name: & \% $\to$ \%\\
\name: & (\%, \astype{Integer}) $\to$ \%\\
}
\Params{
{\em p} & \% & A polynomial\\
{\em n} & \astype{Integer} & The order of integration\\
}
\Retval{\name(p) returns $\int p(x) dx$,
while integrate(s, n) returns $\int \dots \int s(x) dx^n$.}
#endif
		-- TEMPORARY: pretend SHOULD NOT BE NEEDED
		-- lift: (Derivation R, %) -> Derivation %;
		lift: (Derivation(R pretend Ring), %) -> Derivation %;
#if ALDOC
\aspage{lift}
\Usage{\name(D, x')}
\Signature{(\astype{Derivation} R, \%)}{\astype{Derivation} \%}
\Params{
{\em D} & \astype{Derivation} R & A derivation on R\\
{\em x'} & \% & The desired derivative of x\\
}
\Retval{Returns the unique extension of the derivation $D$ such that
$D x = x'$.}
#endif
	}
	if R has Ring then {
		ordinaryPoint: % -> Z;
#if ALDOC
\aspage{ordinaryPoint}
\Usage{\name~p}
\Signature{\%}{\astype{Integer}}
\Params{ {\em p} & \% & A nonzero polynomial\\ }
\Retval{Returns an integer $n$ such that $p(n) \ne 0$.}
#endif
	}
	if R has IntegralDomain then {
		IntegralDomain;
		monicDivide: (%, %) -> (%, %);
#if ALDOC
\aspage{monicDivide}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{(\%, \%)}
\Params{
{\em a} & \% & A polynomial\\
{\em b} & \% & A polynomial whose leading coefficient is a unit in $R$\\
}
\Retval{Returns $(q, r)$ such that $a = b q + r$ and either $r = 0$
or $\deg(r) < \deg(b)$. The leading coefficient of $b$ must be a unit in $R$.}
\seealso{\asexp{monicRemainder}, \asexp{pseudoDivide}}
#endif
		monicRemainder: (%, %) -> %;
		monicRemainder!: (%, %) -> %;
#if ALDOC
\aspage{monicRemainder}
\astarget{\name!}
\Usage{\name(a, b)\\ \name!(a, b)}
\Signature{(\%, \%)}{\%}
\Params{
{\em a} & \% & A polynomial\\
{\em b} & \% & A polynomial whose leading coefficient is a unit in $R$\\
}
\Retval{Returns $r$ such that $a = b q + r$ and either $r = 0$
or $\deg(r) < \deg(b)$. The leading coefficient of $b$ must be a unit in $R$.}
\Remarks{When using \name!($a,b$), the storage used by a is allowed to be
destroyed or reused, so a is lost after this call.
This may cause a to be destroyed, so do not use this unless a has been locally
allocated, and is thus guaranteed not to share space with other polynomials.}
\seealso{\asexp{monicDivide}, \asexp{pseudoRemainder}}
#endif
		pseudoDivide: (%, %) -> (%, %);
#if ALDOC
\aspage{pseudoDivide}
\Usage{\name(a, b)}
\Signature{(\%, \%)}{(\%, \%)}
\Params{
{\em a} & \% & A polynomial\\
{\em b} & \% & A nonzero polynomial\\
}
\Retval{Returns $(q, r)$ such that $c^n a = b q + r$ and either $r = 0$
or $\deg(r) < \deg(b)$, where $c$ is the leading coefficient of $b$ and
$n = \deg(a) - \deg(b) + 1$.}
\seealso{\asexp{pseudoRemainder}}
#endif
		pseudoRemainder: (%, %) -> %;
		pseudoRemainder!: (%, %) -> %;
#if ALDOC
\aspage{pseudoRemainder}
\astarget{\name!}
\Usage{\name(a, b)\\ \name!(a, b)}
\Signature{(\%, \%)}{\%}
\Params{
{\em a} & \% & A polynomial\\
{\em b} & \% & A nonzero polynomial\\
}
\Retval{Returns $r$ such that $c^n a = b q + r$ and either $r = 0$
or $\deg(r) < \deg(b)$, where $c$ is the leading coefficient of $b$ and
$n = \deg(a) - \deg(b) + 1$.}
\Remarks{When using \name!($a,b$), the storage used by a is allowed to be
destroyed or reused, so a is lost after this call.
This may cause a to be destroyed, so do not use this unless a has been locally
allocated, and is thus guaranteed not to share space with other polynomials.}
\seealso{\asexp{pseudoDivide}}
#endif
		resultant: (%, %) -> R;
#if ALDOC
\aspage{resultant}
\Usage{\name(p, q)}
\Signature{(\%, \%)}{R}
\Params{
{\em p} & \% & A polynomial\\
{\em q} & \% & A polynomial\\
}
\Retval{Returns the resultant of p and q.}
#endif
	}
	if R has Field then {
		sparseMultiple: (%, Z) -> %;
#if ALDOC
\aspage{sparseMultiple}
\Usage{\name(p, n)}
\Signature{(\%, \astype{Integer})}{\%}
\Params{
{\em p} & \% & A polynomial\\
{\em n} & \astype{Integer} & A positive integer\\
}
\Retval{Returns a nonzero polynomial $q = \sum_{i=0}^m a_i x^i$
of minimal degree such that $q(x^n)$ is a multiple of $p(x)$.}
#endif
	}
	if R has GcdDomain then {
		DecomposableRing;
		GcdDomain;
		squareFree: % -> (R, Product %);
		squareFreePart: % -> %;
#if ALDOC
\aspage{squareFree,squareFreePart}
\astarget{squareFree}
\astarget{squareFreePart}
\Usage{squareFree~p\\ squareFreePart~p}
\Signatures{
squareFree: & \% $\to$ (R, \astype{Product} \%)\\
squareFreePart: & \% $\to$ \%\\
}
\Params{ {\em p} & \% & A polynomial\\ }
\Descr{squareFree(p) returns $(c, p_1^{e_1} \cdots p_n^{e_n})$ such that
each $p_i$ is squarefree, the $p_i$'s have no common factors, and
$$
p = c\;\prod_{i=1}^n p_i^{e_i}\,,
$$
while squareFreePart(p) returns $p^\ast$ such that $p^\ast$ is squarefree,
$p^\ast \mid p$ and every irreducible factor of $p$ divides $p^\ast$.
}
#endif
	}
	if R has Ring then {
		values: (%, R) -> Generator R;
#if ALDOC
\aspage{values}
\Usage{\name(p, a)}
\Signature{(\%,R)}{\astype{Generator} R}
\Params{
{\em p} & \% & A polynomial\\
{\em a} & R & A scalar\\
}
\Retval{Returns a generator generating the
sequence $p(a), p(a+1), p(a+2),\ldots$}
\Remarks{\name~uses arrays of differences and can be more efficient
that repeated Horner evaluation.}
#endif
	}
	if R has Field then EuclideanDomain;
	if R has Specializable then Specializable;
	default {
		equal?(a:%, b:%, c:%, n:Z):Boolean == {
			n <= 0 => true;
			deg := trailingDegree(a - b * c);
			deg = -1 or deg >= n;
		}

		-- Horner's division of p by x - a,
		-- returns c q and p(a) s.t.  p = q (x - a) + p(a)
		local horner(p:%, c:R, a:R):(%, R) == {
			import from Z;
			assert(~zero? c);
			one? c => Horner(p, a);
			zero? p => (0, 0);
			zero? a => (times!(c, shift(p, -1)), coefficient(p, 0));
			v := leadingCoefficient p;
			q:% := 0;
			for i in prev degree p .. 0 by -1 repeat {
				q := add!(q, c * v, i);
				v := a * v + coefficient(p, i);
			}
			(q, v);
		}

		Horner(p:%, a:R):(%, R) == {
			import from Z;
			zero? p => (0, 0);
			zero? a => (shift(p, -1), coefficient(p, 0));
			v := leadingCoefficient p;
			q:% := 0;
			for i in prev degree p .. 0 by -1 repeat {
				q := add!(q, v, i);
				v := a * v + coefficient(p, i);
			}
			(q, v);
		}

		-- uses Horner's rule
		apply(p:%, a:R):R == {
			import from Z;
			zero? p => 0;
			zero? a => coefficient(p, 0);
			v := leadingCoefficient p;
			for i in prev degree p .. 0 by -1 repeat
				v := a * v + coefficient(p, i);
			v;
		}

		-- uses Horner's rule
		apply(p:%, q:%):% == {
			import from Z;
			zero? p => 0;
			zero? q => coefficient(p, 0)::%;
			v := leadingCoefficient(p)::%;
			for i in degree p - 1 .. 0 by -1 repeat
				v := add!(times!(v, q), coefficient(p, i)::%);
			v;
		}

		-- returns c p x^n, always makes a copy, also for n = 0
		local shift(p:%, c:R, n:Z):% == {
			zero? c => 0;
			one? c => {
				zero? n => copy p;
				shift(p, n);
			}
			q:% := 0;
			pos?:Boolean := n >= 0;
			for term in p repeat {
				(a, d) := term;
				e := d + n;
				if pos? or e >= 0 then q := add!(q, c * a, e);
			}
			q;
		}

		if R has Ring then {
			-- tries 0,1,-1,2,-2,... until a good point is found
			ordinaryPoint(p:%):Z == {
				import from R;
				~zero? p(0@R) => 0;
				n:Z := 1;
				repeat {
					a := n::R;
					~zero? p a => return n;
					~zero? p(-a) => return(-n);
					n := next n;
				}
			}

			values(p:%, a:R):Generator R == {
				import from Array R, I, Z;
				zero? p or zero?(dp := degree p) => generate {
					repeat yield leadingCoefficient p;
				}
				d := machine dp;
				v:Array R := new next d;
				generate {
					for i in 0..d repeat {
						v.i := p(a + i::Z::R);
						yield(v.i);
					}
					for i in prev(d)..0 by -1 repeat {
						for j in 0..i repeat
							v.j := v(j+1)-v.j;
					}
					repeat {
						for i in 1..d repeat
							v.i := v.i+v(i-1);
						yield v.d;
					}
				}
			}
		}

		if R has OrderedArithmeticType then {
			height(p:%):R == {
				h:R := 0;
				for term in p repeat {
					(c, n) := term;
					a := abs c;
					if a > h then h := a;
				}
				h;
			}
		}

		-- TEMPORARY: IF R has RING SHOULD NOT BE NEEDED (COMRING!)
		if R has Ring then {
		if R has CommutativeRing then {
			if R has QRing then {
				integrate(p:%):% == {
					import from Z;
					integrate(p, 1);
				}

				integrate(p:%, k:Z):% == {
					import from I, R;
					zero?(kk := machine k) => p;
					assert(kk > 0);
					q:% := 0;
					for term in p repeat {
						(c, n) := term;
						m := factorial(next n, 1, kk);
						q := add!(q, inv(m) * c, n + k);
					}
					q;
				}
			}

			canonicalUnitNormal?:Boolean == canonicalUnitNormal?$R;

			karatsubaCutoff:I == {
				kx := karatsubaCutoff$R;
				zero? kx => 0;
				max(5, kx quo 2);
			} where { kx:I; }

			-- returns true if a = u x^n and u is a unit,
			-- false otherwise
			local umonom?(a:%):Boolean == {
				import from R;
				assert(~zero? a);
				monomial? a and unit? leadingCoefficient a;
			}

			-- MORE EFFICIENT THAN THE COMRING DEFAULT
			unit?(a:%):Boolean == {
				import from Z, R;
				zero? a => false;
				zero? degree a and unit? leadingCoefficient a;
			}

			-- returns u^{-1} if a = u x^n and u is a unit,
			-- failed otherwise
			local umonom(a:%):Partial R == {
				import from R;
				assert(~zero? a);
				monomial? a => reciprocal leadingCoefficient a;
				failed;
			}

			-- returns (q, u, u^{-1}) s.t. p = u q
			unitNormal(p:%):(%,%,%) == {
				import from R;
				(y, u, uinv) := unitNormal leadingCoefficient p;
				(uinv * p, u::%, uinv::%);
			}

			differentiate(p:%):% == {
				import from Z;
				differentiate(p, 1);
			}

			differentiate(p:%, k:Z):% == {
				import from I, R;
				zero?(kk := machine k) => p;
				assert(kk > 0);
				h:% := 0;
				for term in p repeat {
					(c, n) := term;
					if (e := n - k) >= 0 then {
						m := factorial(next e, 1, kk);
						h := add!(h, m::R * c, e);
					}
				}
				h;
			}

			-- TEMPORARY: pretend SHOULD NOT BE NEEDED
			-- lift(D:Derivation R, xp:%):Derivation % ==
			lift(D:Derivation(R pretend Ring),xp:%):Derivation % =={
				derivation((p:%):% +-> diff(p, D, xp));
			}

			-- TEMPORARY: pretend SHOULD NOT BE NEEDED
			-- local diff(p:%, D:Derivation R, xp:%):% ==
			local diff(p:%,D:Derivation(R pretend Ring),xp:%):% == {
				import from Z, R;
				h:% := 0;
				for term in p repeat {
					(c, n) := term;
					h := add!(h, D c, n);
					if n > 0 then
						h := add!(h, n::R * c, n-1, xp);
				}
				h;
			}

			quotient(p:%, q:%):% == {
				import from Z, R, Partial R;
				assert(~zero? q);
				zero? p => 0;
				one? q => p;
				(a, n) := trailingMonomial q;
				quot!(copy p, q, divideBy(leadingCoefficient q),
					divideBy a, n);
			}

			-- computes p / q, destroying p but not q
			local quot!(p:%,q:%,divByLq:R->R,divByTq:R->R,tdeg:Z):%_
				== {
				import from R;
				TRACE("upolc0::quot!:p = ", p);
				assert(~zero? p);
				assert(~zero? q);
				assert(~one? q);
				qt:% := 0;
				zero?(dq := degree q) => {
					for term in p repeat {
						(a, n) := term;
						qt := add!(qt, divByLq a, n);
					}
					qt;
				}
				dp := degree p;
				d := dp - dq;
				dr := (next d) quo 2;
				low := dq + dr;
				while d >= dr repeat {
					c := divByLq(leadingCoefficient p);
					qt := add!(qt, c, d);
					p := add!(p, -c, d, q, low, dp);
					dp := degree p;
					d := dp - dq;
				}
				high := prev(tdeg + dr);
				(a, n) := trailingMonomial p;
				d := n - tdeg;
				while d < dr and a ~= 0 repeat {
					c := divByTq a;
					qt := add!(qt, c, d);
					p := add!(p, -c, d, q, n, high);
					(a, n) := trailingMonomial p;
					d := n-tdeg;
				}
				qt;
			}

			-- returns p x^n / c, always makes a copy
			local shift(c:R, p:%, n:Z):Partial % == {
				import from Partial R;
				assert(~zero? c);
				assert(~unit? c);
				q:% := 0;
				pos?:Boolean := n >= 0;
				for term in p repeat {
					(a, d) := term;
					u := exactQuotient(a, c);
					failed? u => return failed;
					e := d + n;
					if pos? or e >= 0 then
						q := add!(q, retract u, e);
				}
				[q];
			}

			exactQuotient(p:%, q:%):Partial % == {
				import from Z, R, Partial R;
				assert(~zero? q);
				zero? p => [0];
				one? q => [p];
				-- check first whether trailing degrees divide
				(cp, dp) := trailingMonomial p;
				(cq, dq) := trailingMonomial q;
				dp < dq => failed;
				u := reciprocal(lq := leadingCoefficient q);
				inv? := ~failed? u;
				-- special case where q = lq x^dq
				(dgq := degree q) = dq => {
					inv? => [shift(p, retract u, -dq)];
					shift(lq, p, -dq);
				}
				-- special case where q = a x + b
				inv? and one? dgq => {
					ilq := retract u;
					(qt, v) := horner(p, ilq,
							- ilq*coefficient(q,0));
					zero? v => [qt];
					failed;
				}
				-- general case
				a := copy p;
				uqt:Partial % := {
					inv? => [exquo!(retract u, a, q)];
					-- R cannot be a field at this point
					failed? exactQuotient(cp, cq) =>
						return failed;
					exquo!(a, q);
				}
				failed? uqt => failed;
				equal?(p, retract uqt, q, dgq) => uqt;
				failed;
			}

			-- ilq = inverse of leading coeff of q
			-- does not necessarily return an exact quotient
			-- computes a candidate p / q, destroying p but not q
			local exquo!(ilq:R, p:%, q:%):% == {
				import from Z, R;
				dq := degree q;
				quot:% := 0;
				dp := degree p;
				while (d := dp - dq) >= 0 repeat {
					c := ilq * leadingCoefficient p;
					quot := add!(quot, c, d);
					p := add!(p, - c, d, q, dq, dp);
					dp := degree p;
				}
				quot;
			}

			-- should not be used when lq is a unit
			-- does not necessarily return an exact quotient
			-- computes a candidate p / q, destroying p but not q
			local exquo!(p:%, q:%):Partial % == {
				import from Z, R, Partial R;
				dq := degree q;
				lq := leadingCoefficient q;
				assert(~unit? lq);
				quot:% := 0;
				dp := degree p;
				while (d := dp - dq) >= 0 repeat {
					c := exactQuotient(leadingCoefficient p,
	 							lq);
					failed? c => return failed;
					cc := retract c;
					quot := add!(quot, cc, d);
					p := add!(p, - cc, d, q, dq, dp);
					dp := degree p;
				}
				[quot];
			}
		} }

		-- TEMPORARY: R has RING/COMRING SHOULD NOT BE NEEDED
		if R has Ring then {
		if R has CommutativeRing then {
		if R has IntegralDomain then {
			pseudoDivide(a:%,b:%):(%,%) == pseudoDivide!(copy a, b);
			pseudoRemainder(a:%,b:%):%==pseudoRemainder!(copy a,b);

			pseudoRemainder!(a:%,b:%): % == {
				import from Z, R;
				zero? a => 0;
				da := degree a; db := degree b;
				lb := leadingCoefficient b;
				N := da-db+1;
				b := reductum b;
				while ~zero?(a) and (d := da - db) >= 0 repeat {
					la := leadingCoefficient a;
					a:= add!(times!(lb,reductum a),-la,d,b);
					da := degree a;
					N := prev N;
				}
				zero? N => a;
				times!(lb^N, a);
			}

			local pseudoDivide!(a:%,b:%): (%,%) == {
				import from Z, R;
				zero? a => (0,0);
				da := degree a; db := degree b;
				lb := leadingCoefficient b;
				N := da-db+1;
				b := reductum b;
				q:% := 0;
				while ~zero?(a) and (d := da - db) >= 0 repeat {
					la := leadingCoefficient a;
					a:= add!(times!(lb,reductum a),-la,d,b);
					q := add!(times!(lb, q), la, d);
					da := degree a;
					N := prev N;
				}
				zero? N => (q, a);
				f := lb^N;
				(times!(f, q), times!(f, a));
			}

			-- destroys p
			monicRemainder!(p:%, q:%):% == {
				import from Z, R, Partial R;
				assert(~zero? q);
				zero? p or zero?(dq := degree q) => 0;
				one? p => p;
				lq := leadingCoefficient q;
				assert(unit? lq);
				if ~one?(lq) then
					q := retract(reciprocal lq) * q;
				assert(one? leadingCoefficient q);
				one? dq => p(- coefficient(q, 0))::%;
				monicRemainder1!(p, q, dq);
			}

			monicRemainder(p:%, q:%):% == {
				import from Z, R, Partial R;
				assert(~zero? q);
				zero? p or zero?(dq := degree q) => 0;
				one? p => p;
				lq := leadingCoefficient q;
				assert(unit? lq);
				if ~one?(lq) then
					q := retract(reciprocal lq) * q;
				assert(one? leadingCoefficient q);
				one? dq => p(- coefficient(q, 0))::%;
				monicRemainder1!(copy p, q, dq);
			}

			-- destroys p
			local monicRemainderMonomial1!(p:%, q:%, dq:Z):% == {
				import from Z, R;
				assert(~zero? q); assert(~zero? p);
				assert(dq = degree q); assert(dq > 1);
				assert(one? leadingCoefficient q);
				assert(monomial? q);
				while ~zero? p repeat {
					dp := degree p;
					(d := dp - dq) < 0 => return p;
					p := add!(p, -leadingCoefficient p, dp);
				}
				0;
			}

			-- destroys p
			local monicRemainder1!(p:%, q:%, dq:Z):% == {
				import from Z, R;
				assert(~zero? q); assert(~zero? p);
				assert(dq = degree q); assert(dq > 1);
				assert(one? leadingCoefficient q);
				monomial? q => monicRemainderMonomial1!(p,q,dq);
				while ~zero? p repeat {
					dp := degree p;
					(d := dp - dq) < 0 => return p;
					p := add!(p,-leadingCoefficient p,d,q);
				}
				0;
			}

			monicDivide(p:%, q:%):(%, %) == {
				import from Z, R, Partial R;
				assert(unit? leadingCoefficient q);
				a := retract reciprocal leadingCoefficient q;
				one? degree q => {
					(q, v) := horner(p, a,
							- coefficient(q,0) * a);
					(q, v::%);
				}
				monicDivide!(copy p, q, a, 0);
			}

			-- destroys p and quot, ilq = inverse of lc(q)
			local monicDivide!(p:%, q:%, ilq:R, quot:%):(%, %) == {
				import from Z, R;
				assert(~zero? q);
				assert(one?(ilq * leadingCoefficient q));
				zero? p => (0, 0);
				dq := degree q;
				one? p => { zero? dq => (ilq::%, 0); (0, p) };
				first?:Boolean := true;
				while ~zero? p repeat {
					d := degree p - dq;
					d < 0 => return (quot, p);
					c := leadingCoefficient p * ilq;
					quot := {
						first? => monomial!(quot, c, d);
						add!(quot, c, d);
					}
					p := add!(p, - c, d, q);
					if first? then first? := false;
				}
				(quot, 0);
			}

			-- order at x^n of q
			local umonomorder(n:Z)(q:%):Z == {
				assert(~zero? q);
				assert(n > 1);
				trailingDegree(q) quo n;
			}

			-- return the multiplicity n of a as a root of q
			-- as well as c^n q / (x - a)^n
			local computeRootOrder(c:R, a:R)(q:%):(Z, %) == {
				import from Z;
				assert(~zero? q);
				assert(~zero? a);
				n:Z := 0;
				lastq := q;
				(q, v) := horner(lastq, c, a);
				while zero? v repeat {
					n := next n;
					lastq := q;
					(q, v) := horner(lastq, c, a);
				}
				assert(~zero? v);
				(n, lastq);
			}

			-- return the multiplicity of a as a root of q
			local rootOrder(a:R)(q:%):Z == {
				(n, q) := computeRootOrder(1, a)(q);
				n;
			}

			-- redefined: special cases p = u x^n or p = a x + b
			order(p:%):% -> Z == {
				import from Z, R, Partial R;
				d := degree p;
				assert(~zero? p and ~zero? d);
				-- special case where p = u x^n
				umonom? p => {
					one? d => trailingDegree;
					umonomorder d;
				}
				-- special case where p = a x + b, a unit
				one? d and ~failed?(_
					u := reciprocal leadingCoefficient p) =>
						rootOrder(- coefficient(p,0) *_
								retract u);
				-- general case
				generalOrder p;
			}

			local generalOrder(p:%)(q:%):Z == {
				(n, q) := computeOrder(p)(q);
				n;
			}

			-- order at u^{-1} x^n of q
			local umonomorderquo(u:R, n:Z)(q:%):(Z, %) == {
				assert(~zero? q);
				zero?(m := trailingDegree(q) quo n) => (m, q);
				(m, shift(q, u, -m * n));
			}

			-- redefined: special cases p = u x^n or p = a x + b
			orderquo(p:%):% -> (Z, %) == {
				import from Z, R, Partial R;
				d := degree p;
				assert(~zero? p and ~zero? d);
				-- special case where p = u x^n
				~failed?(u := umonom p) =>
						umonomorderquo(retract u, d);
				-- special case where p = a x + b, a unit
				one? d and ~failed?(_
					u:=reciprocal leadingCoefficient p) => {
						a := retract u;
						computeRootOrder(a,
							- coefficient(p,0) * a);
				}
				-- general case
				computeOrder p;
			}

			-- order of q at p
			local computeOrder(p:%)(q:%):(Z, %) == {
				import from Partial %;
				assert(~zero? p and ~zero? q and ~zero? degree p
							and ~umonom? p);
				n:Z := 0;
				while ~failed?(u := exactQuotient(q,p)) repeat {
					n := next n;
					q := retract u;
				}
				(n, q);
			}
		} } }

		-- TEMPORARY: R has RING/COMRING SHOULD NOT BE NEEDED
		if R has Ring then {
		if R has CommutativeRing then {
		if R has GcdDomain then {
			provablyIrreducible?(a:%):Boolean == {
				import from Z;
				assert(~zero? a);
				one? degree a;
			}

			someFactors(a:%):List % == {
				import from Product %;
				l:List % := empty;
				(c, p) := squareFree a;
				for term in p repeat {
					(b, e) := term; l := cons(b, l);
				}
				l;
			}

			squareFreePart(a:%):% == {
				(g, aa, dummy) :=
					gcdquo(a,differentiate a)$(%@GcdDomain);
				aa;
			}
		} } }

		-- TEMPORARY: R has RING/COMRING/INTDOM SHOULD NOT BE NEEDED
		if R has Ring then {
		if R has CommutativeRing then {
		if R has IntegralDomain then {
		if R has Field then {
			-- TEMPORARY: THOSE DEFAULTS CANNOT BE IN sit_euclid.as
			-- AS LONG AS THE COMPILER DOES EARLY-BINDING
			divide!(a:%, b:%, q:%):(%, %)	== divide(a, b);
			remainder!(a:%, b:%):%		== a rem b;

			divide(a:%, b:%):(%, %) == monicDivide(a, b);
			(a:%) rem (b:%):%	== monicRemainder(a, b);

			(a:%) quo (b:%):% == {
				(q, r) := divide(a, b);
				q;
			}

			euclideanSize(a:%):Z == {
				assert(~zero? a);
				degree a;
			}

			sparseMultiple(p:%, N:Z):% == {
				-- TEMPORARY: pretend SHOULD NOT BE NEEDED
				-- import from I, LinearAlgebra(R, M R);
				import from I, LinearAlgebra(R pretend Field, M R);
				assert(N > 0);
				zero? p or zero?(d := degree p) or one? N => p;
				m := machine d;
				firstDependence(remgen(N, p, m), m)::%;
			}

			-- generates x^{in} mod p for i = 0,1,...
			local remgen(n:Z,p:%,dim:I):Generator V R == generate {
				assert(n > 1);
				v:V R := zero dim;
				vec! := vectorize! v;
				y:% := 1;
				yield vec! y;
				repeat {
					y := remainder!(shift(y, n), p);
					yield vec! y;
				}
			}
		} } } }

		if R has Specializable then {
			specialization(Image:CommutativeRing):_
				PartialFunction(%,Image) == {
				import from Z, R, Image, Partial Image;
				import from PartialFunction(R, Image);
				f := partialMapping(specialization(Image)$R);
				x := random()$Image;
				-- uses Horner's evaluation specializing the
				-- coefficients as we go along, which is more
				-- efficient than computing f p x
				partialFunction((p:%):Partial(Image) +-> {
					zero? p => [0];
					zero? x => f coefficient(p, 0);
					failed?(vv := f leadingCoefficient p) =>
						failed;
					v := retract vv;
					for i in prev degree p..0 by -1 repeat {
						failed?(u:=f coefficient(p,i))=>
							return failed;
						v := x * v + retract u;
					}
					[v];
				})
			}
		}
	}
}

