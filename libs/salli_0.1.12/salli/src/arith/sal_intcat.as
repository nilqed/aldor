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
------------------------------ sal_intcat.as ---------------------------------
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro Z == MachineInteger;

#if ALDOC
\thistype{IntegerType}
\History{Manuel Bronstein}{28/9/98}{created}
\Usage{\this: Category}
\Descr{\this~is the category of types representing integers.}
\begin{exports}
\category{\astype{BooleanArithmeticType}}\\
\category{\astype{HashType}}\\
\category{\astype{InputType}}\\
\category{\astype{OrderedArithmeticType}}\\
\category{\astype{OutputType}}\\
\category{\astype{SerializableType}}\\
\asexp{bit?}:
& (\%, \astype{MachineInteger}) $\to$ \astype{Boolean} & check a bit\\
\asexp{clear}: & (\%, \astype{MachineInteger}) $\to$ \% & clear a bit\\
\asexp{coerce}:
& \astype{MachineInteger} $\to$ \% & conversion from machine integer\\
\asexp{divide}: & (\%, \%) $\to$ (\%, \%) & Euclidean division\\
\asexp{even?}: & \% $\to$ \astype{Boolean} & test whether a number is even\\
\asexp{factorial}: & \% $\to$ \% & factorial\\
\asexp{gcd}: & (\%, \%) $\to$ \% & greatest common divisor\\
\asexp{lcm}: & (\%, \%) $\to$ \% & least common multiple\\
\asexp{length}: & \% $\to$ \astype{MachineInteger} & number of bits\\
\asexp{machine}:
& \% $\to$ \astype{MachineInteger} & conversion to a machine integer\\
\asexp{mod}: & (\%, \%) $\to$ \% & remainder\\
             & (\%, \astype{MachineInteger}) $\to$ \astype{MachineInteger} & \\
\asexp{nthRoot}: & (\%, \%) $\to$ (\astype{Boolean}, \%) & $\sth{n}$--root\\
\asexp{odd?}: & \% $\to$ \astype{Boolean} & test whether a number is odd\\
\asexp{quo}: & (\%, \%) $\to$ \% & quotient\\
\asexp{random}: & () $\to$ \% & random integer\\
                & \astype{MachineInteger} $\to$ \% & \\
\asexp{rem}: & (\%, \%) $\to$ \% & remainder\\
\asexp{set}: & (\%, \astype{MachineInteger}) $\to$ \% & set a bit\\
\asexp{shift}: & (\%, \astype{MachineInteger}) $\to$ \% & shift\\
\asexp{shift!}: & (\%, \astype{MachineInteger}) $\to$ \% & in--place shift\\
\end{exports}
#endif

define IntegerType:Category ==
	Join(OrderedArithmeticType, BooleanArithmeticType, HashType,
			InputType, OutputType, SerializableType) with {
		bit?: (%, Z) -> Boolean;
		clear: (%, Z) -> %;
		set: (%, Z) -> %;
#if ALDOC
\aspage{bit?,clear,set}
\astarget{bit?}
\astarget{clear}
\astarget{set}
\Usage{bit?(a, n)\\ clear(a, n)\\ set(a, n)}
\Signatures{
bit?: & (\%, \astype{MachineInteger}) $\to$ \astype{Boolean}\\
clear, set: & (\%, \astype{MachineInteger}) $\to$ \%\\
}
\Params{
{\em a} & \% & an integer\\
{\em n} & \astype{MachineInteger} & a nonnegative machine integer\\
}
\Retval{bit?(a, n) returns \true if the $\sth{n}$ bit of a is 1, \false if it
is 0, while clear(a, n) and set(a, n) return copies of a where the $\sth{n}$ bit
is set respectively to 0 and 1. For all 3 functions,
the rightmost bit of a is the $\sth{0}$ bit and so on.}
#endif
		coerce: Z -> %;
		machine: % -> Z;
#if ALDOC
\aspage{coerce,machine}
\astarget{coerce}
\astarget{machine}
\Usage{n::\%\\ machine~a}
\Signatures{
coerce: & \astype{MachineInteger} $\to$ \%\\
machine: & \% $\to$ \astype{MachineInteger}\\
}
\Params{
{\em a} & \% & an integer\\
{\em n} & \astype{MachineInteger} & a machine integer\\
}
\Retval{n::\% returns n converted to the current type, while machine(a)
returns the low machine word of a converted to a \astype{MachineInteger}.
That operation can cause a loss of precision if a is greater than a machine
word.}
#endif
		divide: (%, %) -> (%, %);
		mod: (%, Z) -> Z;
		mod: (%, %) -> %;
		quo: (%, %) -> %;
		rem: (%, %) -> %;
#if ALDOC
\aspage{divide,mod,quo,rem}
\astarget{divide}
\astarget{mod}
\astarget{quo}
\astarget{rem}
\Usage{divide(a, b)\\ a mod n\\ a mod b\\ a quo b\\ a rem b}
\Signatures{
divide: & (\%,\%) $\to$ (\%, \%)\\
mod,quo,rem: & (\%,\%) $\to$ \%\\
mod: & (\%,\astype{MachineInteger}) $\to$ \astype{MachineInteger}\\
}
\Params{
{\em a,b} & \% & integers, $b \ne 0$\\
{\em n} & \astype{MachineInteger} & a nonzero machine integer\\
}
\Retval{$a$ mod $b$ (resp.~$a$ mod $n$) returns $m$ such that $0 \le m < |b|$
(resp.~$0 \le m < |n|$) and $a \equiv m \pmod b$ (resp $n$),
while $a$ rem $b$ returns $r$ such that $-|b| < r < |b|$ and
$a \equiv r \pmod b$,
$a$ quo $b$ returns $(a - (a$ rem $b)) / b$,
and divide(a, b) returns the pair (a quo b, a rem b).}
\Remarks{mod returns a unique remainder modulo b, but is more expensive
to compute than rem, and is not guaranteed to be compatible with the
result of quo. The version whose second argument is a
\astype{MachineInteger} allows for more efficient implementations.}
#endif
		even?: % -> Boolean;
		odd?: % -> Boolean;
#if ALDOC
\aspage{even?,odd?}
\astarget{even?}
\astarget{odd?}
\Usage{even?~a\\odd?~a}
\Signature{\%}{\astype{Boolean}}
\Params{ {\em a} & \% & an integer\\ }
\Retval{even?(a) and odd?(a) return \true when a is even, respectively odd,
\false otherwise.}
#endif
		factorial: % -> %;
#if ALDOC
\aspage{factorial}
\Usage{\name~a}
\Signature{\%}{\%}
\Params{ {\em a} & \% & a nonnegative integer\\ }
\Retval{Returns $a! = \prod_{i=1}^a i$.}
#endif
		gcd: (%, %) -> %;
		lcm: (%, %) -> %;
#if ALDOC
\aspage{gcd,lcm}
\astarget{gcd}
\astarget{lcm}
\Usage{gcd(a, b)\\ lcm(a, b)}
\Signature{(\%,\%)}{\%}
\Params{ {\em a,b} & \% & integers\\ }
\Retval{gcd(a, b) and lcm(a, b) return respectively a greatest common divisor
and a least common multiple of a and b.}
#endif
		integer: Literal -> %;
		length: % -> Z;
#if ALDOC
\aspage{length}
\Usage{\name~a}
\Signature{\%}{\astype{MachineInteger}}
\Params{ {\em a} & \% & an integer\\ }
\Retval{Returns the number of binary bits of a, \ie n such that
\asexp{bit?}$(a, n-1)$ is \true and \asexp{bit?}$(a, m)$
is \false for $m \ge n$.}
#endif
		nthRoot: (%, %) -> (Boolean, %);
#if ALDOC
\aspage{nthRoot}
\Usage{\name(a, b)}
\Signature{(\%,\%)}{(\astype{Boolean},\%)}
\Params{
{\em a} & \% & an integer\\
{\em b} & \% & a positive integer\\
}
\Retval{Returns (found?, n) such that
$a = n^b$ if found?~is \true. Otherwise, found?~is \false~and
$$
n^b < a < (n+1)^b\,.
$$
}
#endif
		random: () -> %;
		random: Z -> %;
#if ALDOC
\aspage{random}
\Usage{\name()\\ \name~n}
\Signatures{
\name: () $\to$ \%\\
\name: \astype{MachineInteger} $\to$ \%\\
}
\Params{ {\em n} & \astype{MachineInteger} & a positive size\\ }
\Retval{\name() returns a random integer, while \name(n) returns
a random integer with $n$ limbs.}
#endif
		shift: (%, Z) -> %;
		shift!:(%, Z) -> %;
#if ALDOC
\aspage{shift}
\astarget{\name!}
\Usage{\name(a, n)\\ \name!(a, n)}
\Signature{(\%, \astype{MachineInteger})}{\%}
\Params{
{\em a} & \% & an integer\\
{\em n} & \astype{MachineInteger} & a machine integer\\
}
\Retval{Returns $a$ shifted left $n$ times if $n \ge 0$,
shifted right $-n$ times if $n \le 0$.}
\Remarks{\name!~does not make a copy of $x$, which is therefore
modified after the call. It is unsafe to use the variable $x$
after the call, unless it has been assigned to the result
of the call, as in {\tt x := \name!(x, n)}.}
#endif
		default {
			lcm(a:%, b:%):% 	== (a * b) quo gcd(a, b);
			next(a:%):%		== a + 1;
			prev(a:%):%		== a - 1;
			set(a:%, n:Z):%		== a \/ shift(1, n);
			clear(a:%, n:Z):%	== a /\ ~(shift(1, n));
			hash(a:%):Z		== machine a;
			odd?(a:%):Boolean	== ~even? a;
			shift!(a:%, n:Z):%	== shift(a, n);
			(a:%) mod (n:Z):Z	== machine(a mod (n::%));

			-- THE IMPLEMENTATION FROM Machine USES a % 2!!!
			even?(a:%):Boolean	== zero?(a /\ 1);

			factorial(n:%):% == {
				assert(n >= 0);
				m:% := 1; p := n;
				while p > 1 repeat {
					m := times!(m, p);
					p := prev p;
				}
				m;
			}

			(a:%) mod (b:%):% == {
				assert(b ~= 0);
				(r := a rem b) < 0 => r + abs b;
				r;
			}
		}
}
