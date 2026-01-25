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
------------------------------- sit_euclid.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{EuclideanDomain}
\History{Manuel Bronstein}{13/12/94}{created}
\Usage{\this: Category}
\Descr{\this~is the category of commutative Euclidean domains.}
\begin{exports}
\category{\astype{GcdDomain}}\\
\asexp{diophantine}: & (\%, \%, \%) $\to$ \astype{Partial} \% &
Solve a linear diophantine equation\\
\asexp{divide}: & (\%, \%) $\to$ (\%, \%) & Euclidean division\\
\asexp{divide!}: & (\%, \%, \%) $\to$ (\%, \%) & In--place Euclidean division\\
\asexp{euclid}: & (\%, \%) $\to$ \% & Euclidean gcd\\
\asexp{euclid!}: & (\%, \%) $\to$ \% & In--place Euclidean gcd\\
\asexp{euclideanSize}:
& \% $\to$ \astype{Integer} & Size function of the domain\\
\asexp{extendedEuclidean}:
& (\%, \%) $\to$ (\%, \%, \%) & Extended Euclidean Algorithm\\
& (\%, \%, \%) $\to$ \astype{Partial}(\%, \%) &\\
\asexp{quo}: & (\%, \%) $\to$ \% & Quotient\\
\asexp{rem}: & (\%, \%) $\to$ \% & Remainder\\
\asexp{remainder!}: & (\%, \%) $\to$ \% & In--place remainder\\
\end{exports}
#endif

define EuclideanDomain: Category == GcdDomain with {
	diophantine: (%, %, %) -> Partial %;
#if ALDOC
\aspage{diophantine}
\Usage{\name(a, b, m)}
\Signature{(\%, \%, \%)}{\astype{Partial} \%}
\Params{
{\em a} & \% & An element of the ring\\
{\em b} & \% & The right hand side of the equation\\
{\em m} & \% & The nonzero modulus\\
}
\Retval{If the diophantine equation $a x \equiv b \pmod m$ has solutions in
the ring, returns a solution x such that either $x = 0$ or
$\abs x < \abs m$. Returns \failed if the equation has no solution.}
#endif
	divide: (%, %) -> (%, %);
	quo: (%, %) -> %;
	rem: (%, %) -> %;
#if ALDOC
\aspage{divide,quo,rem}
\astarget{divide}
\astarget{quo}
\astarget{rem}
\Usage{divide(a, b)\\a quo b\\ a rem b}
\Signatures{
divide: & (\%,\%) $\to$ (\%, \%)\\
quo,rem: & (\%,\%) $\to$ \%\\
}
\Params{ {\em a,b} & \% & Element of the ring, $y \ne 0$\\ }
\Retval{$a$ rem $b$ returns $r$ such that either $r = 0$
or $0 \le \abs r < \abs b$ and $a \equiv r \pmod b$,
$a$ quo $b$ returns $q$ such that $a - b q = 0$
or $0 \le \abs{a - bq} < \abs b$,
and divide(a, b) returns the pair (a quo b, a rem b).}
#endif
	divide!: (%, %, %) -> (%, %);
#if ALDOC
\aspage{divide!}
\Usage{\name(x, y, z)}
\Signature{(\%, \%, \%)}{(\%, \%)}
\Params{
{\em x} & \% & An element of the ring (to be destroyed)\\
{\em y} & \% & An element of the ring\\
{\em z} & \% & A placeholder for the quotient (to be destroyed)\\
}
\Retval{Returns $(q, r)$ such that $x = q y + r$ and either $r = 0$
or $0 \le \abs r < \abs x$,
where the storage used by x and z is allowed to be destroyed or reused,
so x and z is lost after this call.}
\Remarks{This function may cause x and z to be destroyed,
so do not use it unless x and z have been locally allocated,
and are guaranteed not to share space
with other elements. Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
\seealso{\asexp{remainder!}}
#endif
	euclid: (%, %) -> %;
	euclid!: (%, %) -> %;
#if ALDOC
\aspage{euclid}
\astarget{\name!}
\Usage{\name(x, y)\\ \name!(x, y)}
\Signature{(\%, \%)}{\%}
\Params{ {\em x,y} & \% & Elements of the ring\\ }
\Retval{Returns $\gcd(x, y)$ computed by the Euclidean algorithm.
When using \name!(x, y), 
the storage used by x and y is allowed
to be destroyed or reused, so x and y are lost after this call.}
\Remarks{The call \name!(x, y) may cause x and y to be destroyed,
so do not use it unless
x and y have been locally allocated, and are guaranteed not to share space
with other elements. Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
\seealso{\asfunc{GcdDomain}{gcd}, \asfunc{GcdDomain}{gcd!}}
#endif
	euclideanSize: % -> Integer;
#if ALDOC
\aspage{euclideanSize}
\Usage{\name~x}
\Signature{\%}{\astype{Integer}}
\Params{ {\em x} & \% & A nonzero element of the ring\\ }
\Retval{Returns $\abs x$, the euclidean size of x. It is connected
to the Euclidean remainder, in that the remainder r of a by b is either 0,
or satisfies $0 \le \abs r < \abs b$.}
#endif
	extendedEuclidean: (%, %) -> (%, %, %);
	extendedEuclidean: (%, %, %) -> Partial Cross(%, %);
#if ALDOC
\aspage{extendedEuclidean}
\Usage{\name(a, b)\\ \name(a, b, c)}
\Signatures{
\name: & (\%, \%) $\to$ (\%, \%, \%)\\
\name: & (\%, \%, \%) $\to$ \astype{Partial}(\%, \%)\\
}
\Params{ {\em a,b,c} & \% & Elements of the ring\\ }
\Retval{
\name(a, b) returns $(g, x, y)$ such that $g = \gcd(a, b) = a x + b y$.\\
\name(a, b, c) returns either a solution $(x, y)$ of the
diophantine equation $a x + b y = c$, or \failed if it has
no solution in the ring.\\
For the values returned by both calls, either $x = 0$ or
$\abs x < \abs b$.}
#endif
	remainder!: (%, %) -> %;
#if ALDOC
\aspage{remainder!}
\Usage{\name(x, y)}
\Signature{(\%, \%)}{\%}
\Params{
{\em x} & \% & An element of the ring (to be destroyed)\\
{\em y} & \% & An element of the ring\\
}
\Retval{Returns the remainder of x by y,
where the storage used by x is allowed
to be destroyed or reused, so x is lost after this call.}
\Remarks{This function may cause x to be destroyed, so do not use it unless
x has been locally allocated, and is guaranteed not to share space
with other elements. Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
#endif
	default {
		macro PCC			== (% pretend CopyableType);
		local copy?:Boolean		== % has CopyableType;
		divide(a:%, b:%):(%, %)		== (a quo b, a rem b);
		euclid!(p:%, q:%):%		== euclid!(p, q, remainder!);
		local div(p:%, q:%, r:%):(%, %)	== divide(p, q);

		-- TEMPORARY: THOSE DEFAULTS SHOULD BE COMMENTED OUT
		-- AS LONG AS THE COMPILER DOES EARLY-BINDING IN OTHER DEFAULTS
		-- divide!(a:%, b:%, q:%):(%, %)	== divide(a, b);
		-- remainder!(a:%, b:%):%		== a rem b;

		-- uses in-place only when % has CopyableType;
		euclid(p:%, q:%):% == {
			copy? => euclid!(copy(p)$PCC, copy(q)$PCC, remainder!);
			euclid!(p, q, rem);
		}

		-- uses in-place only when % has CopyableType;
		local halfEuclid0(p:%, q:%):(%, %) == {
			copy? => halfEuclid!(p, copy(q)$PCC, divide!);
			halfEuclid!(p, q, div);
		}

		-- uses in-place only when % has CopyableType;
		local halfEuclid(p:%, q:%):(%, %) == {
			copy? => halfEuclid!(copy(p)$PCC, copy(q)$PCC, divide!);
			halfEuclid!(p, q, div);
		}

		-- solves a x = b mod m, i.e. a x + m y = b
		diophantine(a:%, b:%, m:%):Partial % == {
			assert(~zero? m);
			zero?(b := b rem m) => [0];
			zero?(a := a rem m) => failed;
			(g, c) := halfEuclid0(a, m);
			failed?(u := exactQuotient(b, g)) => u;
			[remainder!(times!(c, retract u), m)];
		}

		-- solves a x + b y = c, guarantees x reduced modulo b
		extendedEuclidean(a:%, b:%, c:%):Partial Cross(%, %) == {
			zero? c => [(0, 0)];
			import from Partial %;
			zero? b => {
				zero? a or failed?(u := exactQuotient(c, a)) =>
					failed;
				[(retract u, 0)];
			}
			zero? a => {
				failed?(u := exactQuotient(c, b)) => failed;
				[(0, retract u)];
			}
			(g, x) := halfEuclid(a, b);
			failed?(u := exactQuotient(c, g)) => failed;
			x := remainder!(times!(x, retract u), b);
			[x, quotient(c - a * x, b)];
		}

		-- returns (g, x, y) where g = gcd(a,b) = a x + b y
		-- guarantees x reduced modulo b
		extendedEuclidean(a:%, b:%):(%, %, %) == {
			zero? b => (a, 1, 0);
			zero? a => (b, 0, 1);
			(g, x) := halfEuclid(a, b);
			x := remainder!(x, b);
			(g, x, quotient(g - a * x, b));
		}

		-- destroys both a and b if div! destroys 1st and last arg
		-- if exported, must handle the case a or b = 1 separately
		local halfEuclid!(a:%, b:%, div!:(%,%,%) -> (%,%)):(%, %) == {
			import from Integer;
			zero? b => (a, 1); zero? a => (b, 1);
			a1:% := 1; b1:% := 0; q:% := 0;
			if euclideanSize a < euclideanSize b then {
				(a, b) := (b, a);
				(a1, b1) := (b1, a1);
			}
			while ~zero? b repeat {
				temp := b;
				(q, b) := div!(a, b, q);
				a := temp;
				temp1 := b1;
				b1 := add!(a1, times!(minus! q, b1));
				a1 := temp1;
			}
			(a, a1);
		}

		-- destroys both p and q if rem! destroys its 1st argument
		euclid!(p:%, q:%, rem!:(%, %) -> %):% == {
			import from Integer;
			zero? q => p; zero? p => q;
			one? p or one? q => 1;
			if euclideanSize p < euclideanSize q then (p,q):=(q,p);
			while q ~= 0 repeat {
				temp := q;
				q := rem!(p, q);
				p := temp;
			}
			p;
		}
	}
}
