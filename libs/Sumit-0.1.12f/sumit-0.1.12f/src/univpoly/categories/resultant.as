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
----------------------    resultant.as  ----------------------
#include "sumit"

#if ASDOC
\thistype{Resultant}
\History{Thom Mulders}{25 June 96}{created}
\Usage{import from \this(R,P)}
\Params{
{\em R} & IntegralDomain & Coefficient ring for the polynomials\\
{\em P} & UnivariatePolynomialCategory0 R & A polynomial ring\\
}
\begin{exports}
lastSPRS: & (P,P) $\to$ P & last non-zero remainder in the SPRS\\
extendedLastSPRS: & (P,P) $\to$ (P,P,P) &
extended last non-zero remainder in the SPRS\\
resultant: & (P,P) $\to$ R & polynomial resultant\\
SPRS: & (P,P) $\to$ List P & Subresultant Polynomial Remainder Sequence\\
subResultantGcd: & (P,P) $\to$ P & GCD\\
\end{exports}
\Descr{
\this(R,P) implements polynomial resultant computations.
}
#endif

Resultant(R:IntegralDomain,P:UnivariatePolynomialCategory0 R ): with {

	lastSPRS: (P,P) -> P;
#if ASDOC
\aspage{lastSPRS}
\Usage{\name(a,b)}
\Signature{(P,P)}{P}
\Params{
{\em a,b} & P & Two polynomials\\
}
\Descr{
\name(a,b) returns the last non-zero remainder in the subresultant
polynomial remainder sequence of {\em a} and {\em b}. {\em a} and
{\em b} both should be non-zero and $\deg(a)$ should be at least
$\deg(b)$.
}
#endif

	extendedLastSPRS: (P,P) -> (P,P,P);
#if ASDOC
\aspage{extendedLastSPRS}
\Usage{\name(a,b)}
\Signature{(P,P)}{(P,P,P)}
\Params{
{\em a,b} & P & Two polynomials\\
}
\Descr{
\name(a,b) returns $(r,s,t)$, where $r$ is the last non-zero remainder in the
subresultant polynomial remainder sequence of {\em a} and {\em b} and $s,t$ are
polynomials such that $r=sa+tb$. {\em a} and
{\em b} both should be non-zero and $\deg(a)$ should be at least
$\deg(b)$.
}
#endif

	resultant: (P,P) -> R;
#if ASDOC
\aspage{resultant}
\Usage{\name(a,b)}
\Signature{(P,P)}{R}
\Params{
{\em a,b} & P & Two polynomials\\
}
\Descr{
\name(a,b) returns the resultant of {\em a} and {\em b}. {\em a} and
{\em b} both should be non-zero. 
}
#endif

	SPRS: (P,P) -> List P;
#if ASDOC
\aspage{SPRS}
\Usage{\name(a,b)}
\Signature{(P,P)}{List P}
\Params{
{\em a,b} & P & Two polynomials\\
}
\Descr{
\name(a,b) returns the list of remainders in the subresultant
polynomial remainder sequence of {\em a} and {\em b}. {\em a} and
{\em b} both should be non-zero and $\deg(a)$ should be at least
$\deg(b)$. The list has increasing degree, i.e. the first element in
the list is the last remainder in the remainder sequence.
}
#endif

	if R has GcdDomain then {
		subResultantGcd: (P,P) -> P;
#if ASDOC
\aspage{subResultantGcd}
\Usage{\name(a,b)}
\Signature{(P,P)}{P}
\Params{
{\em a,b} & P & Two polynomials\\
}
\Descr{
\name(a,b) returns the last non-zero remainder in the subresultant
polynomial remainder sequence of either {\em a} and {\em b} or {\em b} and
{\em a}. If R is a Gcd domain, this is then $\gcd(a, b)$. Also returns
$\gcd(a,b)$ if either $a = 0$ or $b = 0$.}
#endif
	}

} == add {

-- See also: W.S. Brown: The subresultant PRS algorithm

	macro SI == SingleInteger;
	macro Z == Integer;

	import from SI,Z;

	-- degree a should be at least degree b
	local resultant!(a:P, b:P): R == {

		ASSERT(~zero? a); ASSERT(~zero? b);
		u1 := a; u2 := b;
		du1 := degree u1; du2 := degree u2;
		ASSERT(du1 >= du2);
		delta := du1 - du2;
		h:R := 1;
		l:R := 1;
		cont?:Boolean := true;

		while cont? repeat {
			r := pseudoRemainder!(u1,u2);
			if (cont? := ~zero? r) then {
				{
					delta=0 => {};
					delta=1 => h := l;
					h := quotient(l^delta,h^(delta-1));
				}
				delta := degree u1 - degree u2;
				beta  := -l * (-h)^delta;
				u1 := u2;
				l := leadingCoefficient u2;
				u2 := apply( (x:R):R +-> quotient(x,beta), r);
			}
          	}
		degree u2 > 0 => 0;
		degree u1 = 1 => leadingCoefficient u2;
		h := quotient(l^delta,h^(delta-1));
		delta := degree u1 -degree u2;
		l := leadingCoefficient u2;
		quotient(l^delta,h^(delta-1));
	}

	resultant(a:P,b:P): R == {
		ASSERT(~zero? a); ASSERT(~zero? b);
		copya := copy a; copyb := copy b;
		da := degree a;
		db := degree b;
		da >= db => resultant!(copya, copyb);
		even? (da*db) => resultant!(copyb, copya);
		- resultant!(copyb, copya);
	}

	SPRS(a:P,b:P): List P == {
		ASSERT(~zero? a); ASSERT(~zero? b);

		import from R;

		list := [b,a];
		u1 := copy a; u2 := copy b;
		du1 := degree u1; du2 := degree u2;
		ASSERT(du1 >= du2);
		delta := du1 - du2;
		h:R := 1;
		l:R := 1;
		cont?:Boolean := true;

		while cont? repeat {
			r := pseudoRemainder!(u1,u2);
			if (cont? := ~zero? r) then {
				{
					delta=0 => {};
					delta=1 => h := l;
					h := quotient(l^delta,h^(delta-1));
				}
				delta := degree u1 - degree u2;
				beta  := -l * (-h)^delta;
				u1 := u2;
				l := leadingCoefficient u2;
				u2 := apply( (x:R):R +-> quotient(x,beta), r);
				list := cons(copy u2,list);
			}
          	}

		list;
	}

	if R has GcdDomain then {
		subResultantGcd(a:P,b:P):P == {
			import from R;
			zero? a => b; zero? b => a;
			(ca, a) := primitive a;
			(cb, b) := primitive b;
			g := {
				degree a >= degree b => lastSPRS(a, b);
				lastSPRS(b, a);
			}
			gcd(ca, cb) * primitivePart g;
		}
	}

	lastSPRS(a:P,b:P): P == {

		ASSERT(~zero? a); ASSERT(~zero? b);

		import from R;

		u1 := copy a; u2 := copy b;
		du1 := degree u1; du2 := degree u2;
		ASSERT(du1 >= du2);
		delta := du1 - du2;
		h:R := 1;
		l:R := 1;
		cont?:Boolean := true;

		while cont? repeat {
			r := pseudoRemainder!(u1,u2);
			if (cont? := ~zero? r) then {
				{
					delta=0 => {};
					delta=1 => h := l;
					h := quotient(l^delta,h^(delta-1));
				}
				delta := degree u1 - degree u2;
				beta  := -l * (-h)^delta;
				u1 := u2;
				l := leadingCoefficient u2;
				u2 := apply( (x:R):R +-> quotient(x,beta), r);
			}
          	}

		u2;

	}

	extendedLastSPRS(a:P,b:P): (P,P,P) == {

		ASSERT(~zero? a); ASSERT(~zero? b);

		import from R;
		u1 := copy a; u2 := copy b;
		du1 := degree u1; du2 := degree u2;
		ASSERT(du1 >= du2);
		s1:P := 1; s2:P := 0;
		t1:P := 0; t2:P := 1;
		delta := du1 - du2;
		h:R := 1;
		l:R := 1;
		cont?:Boolean := true;

		while cont? repeat {
			(q,r) := pseudoDivide(u1,u2);
--print << u1 << newline << u2 <<newline << q << newline << r << newline << newline;
			if (cont? := ~zero? r) then {
				{
					delta=0 => {};
					delta=1 => h := l;
					h := quotient(l^delta,h^(delta-1));
				}
				delta := degree u1 - degree u2;
				beta  := -l * (-h)^delta;
				u1 := u2;
				l := leadingCoefficient u2;
				alpha := l^(delta+1);
				s := apply( (x:R):R +-> quotient(x,beta), alpha*s1-q*s2);
				s1 := s2; s2 := s;
				t := apply( (x:R):R +-> quotient(x,beta), alpha*t1-q*t2);
				t1 := t2; t2 := t;
				u2 := apply( (x:R):R +-> quotient(x,beta), r);
			}
          	}

		(u2,s2,t2);

	}

}

