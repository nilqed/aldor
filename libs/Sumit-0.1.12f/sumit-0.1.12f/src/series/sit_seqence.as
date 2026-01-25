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
----------------------------- sit_seqence.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I == MachineInteger;
	Z == Integer;
	S == Stream;
	TREE == ExpressionTree;
}

#if ALDOC
\thistype{Sequence}
\History{Manuel Bronstein}{30/5/2000}{created}
\Usage{ import from \this~R}
\Params{
{\em R} & \astype{SumitType} & The coefficient domain\\
        & \astype{ArithmeticType} &\\
}
\Descr{\this~R implements infinite sequences with coefficients in R.}
\begin{exports}
\category{\astype{LinearStructureType} R}\\
\category{\astype{UnivariateFreeAlgebra} R}\\
\asexp{\#}: & \% $\to$ Z & number of computed elements\\
\asexp{bound}:
& \% $\to$ \astype{MachineInteger} & upper bound on the support size\\
\asexp{finite?}:
& \% $\to$ \astype{Boolean} & check whether the support is finite\\
\asexp{sequence}: & \astype{Stream} R $\to$ \% & create a sequence\\
\end{exports}
\begin{exports}[if R has \astype{Ring} then]
\asexp{random}: & () $\to$ \% & random sequence\\
\end{exports}
#endif

Sequence(R:Join(ArithmeticType, SumitType)):
	Join(LinearStructureType R, UnivariateFreeAlgebra R) with {
		#: % -> I;
#if ALDOC
\aspage{\#}
\Usage{\name~s}
\Signature{\%}{\astype{MachineInteger}}
\Params{ {\em s} & \% & a sequence\\ }
\Retval{Returns the number of elements of $s$ that have been computed.}
#endif
		bound: % -> I;
		finite?: % -> Boolean;
#if ALDOC
\aspage{bound,finite?}
\astarget{bound}
\astarget{finite?}
\Usage{bound~s\\finite?~s}
\Signatures{
bound: & \% $\to$ \astype{MachineInteger} \\
finite?: & \% $\to$ \astype{Boolean}\\
}
\Params{ {\em s} & \% & a sequence\\ }
\Retval{finite?(s) returns \true if s is known
to have finite support and \false otherwise, while
bound(s) returns $n \ge 0$ if s is known
to have finite support and $s.m = 0$ for $m \ge n$, $-1$ otherwise.}
#endif
		if R has Ring then {
			random: () -> %;
#if ALDOC
\aspage{random}
\Usage{\name()}
\Signature{()}{\%}
\Retval{Returns a sequence with random entries.}
#endif
		}
		sequence: Stream R -> %;
#if ALDOC
\aspage{sequence}
\Usage{\name~s}
\Signature{\astype{Stream} R}{\%}
\Params{ {\em s} & \astype{Stream} R & a stream\\ }
\Retval{Returns $s$ viewed as a sequence.}
#endif
} == S R add {
	Rep == S R;
	import from Rep;

	0:%				== sequence stream(0$R);
	1:%				== 1$R :: %;
	monom:%				== monomial(1$R, 1$Z);
	local dummy:Symbol		== { import from String; -"dummy" }
	coefficient(s:%, n:Z):R		== s(machine n);
	setCoefficient!(s:%,n:Z,c:R):%	== { s(machine n) := c; s }
	minus!(s:%):%			== { zero? s => 0; map!(-$R) s; }
	- (s:%):%			== { zero? s => 0; map(-$R) s; }
	map!(f:R -> R)(s:%):%		== sequence map!(f)(rep s);
	apply(s:%, x:TREE):TREE		== extree s;
	add!(s:%, c:R, n:Z, t:%):%	== add!(s, c * shift(t, n));
	coefficients(s:%):Generator R	== generator rep s;
	finite?(s:%):Boolean		== { import from I; 0 <= bound s }
	sequence(s:S R):%		== per s;
	bracket(g:Generator R):%	== { import from R;sequence stream(g,0)}
	(p:TextWriter) << (s:%):TextWriter	== p(s, dummy);

	if R has Ring then {
		random():% == { import from R; sequence stream(random$R) }
	}

	bound(s:%):I == {
		import from Boolean, R, Partial R;
		(c, u) := constant rep s;
		c < 0 or ~zero?(retract u) => -1;
		c;
	}

	shift(s:%, n:Z):% == {
		import from I, Partial R;
		zero?(nn := machine n) or zero? s => s;
		(cs, u) := constant(rs := rep s);
		cs  < 0 => {
			nn < 0 => sequence stream(0, (m:I):R +-> rs(m-nn));
			sequence stream(0, (m:I):R +-> { m<nn => 0; rs(m-nn) });
		}
		c := retract u;
		nn < 0 => sequence stream(0, (m:I):R +-> rs(m-nn), cs+nn, c);
		sequence stream(0, (m:I):R +-> { m<nn=>0; rs(m-nn) }, cs+nn, c);
	}

	add!(s:%, c:R, n:Z):% == {
		assert(n >= 0);
		zero? s => monomial(c, n);
		nn := machine n;
		rs := rep s;
		rs.nn := rs.nn + c;
		s;
	}

	(s:%) = (t:%):Boolean == {
		import from Pointer, I, R, Partial R;
		(cs, us) := constant(rs := rep s);
		(ct, ut) := constant(rt := rep t);
		cs >= 0 => ct >= 0 and retract us = retract ut
						and equal?(rs, rt, max(cs, ct));
		ct < 0 and (s pretend Pointer) = (t pretend Pointer);
	}

	zero?(s:%):Boolean == {
		import from Z, R;
		zero? coefficient(s, 0) and constant? s;
	}

	one?(s:%):Boolean == {
		import from Z, R;
		one? coefficient(s, 0) and constant? s;
	}

	local constant?(s:%):Boolean == {
		import from I;
		(c, u) := constant rep s;
		zero? c;
	}

	monomial(c:R, n:Z):% == {
		import from I;
		zero? c => 0;
		nn := machine n;
		sequence stream(0, (m:I):R +-> { m = nn => c; 0 }, next nn, 0);
	}

	coerce(c:R):% == {
		import from I;
		zero? c => 0;
		sequence stream(0, (m:I):R +-> c, 1, 0);
	}

	map(f:R -> R)(s:%):% == {
		import from I, Partial R;
		(cs, us) := constant(rs := rep s);
		cs < 0 => sequence stream(0, (m:I):R +-> f(rs.m));
		sequence stream(0, (m:I):R +-> f(rs.m), cs, f(retract us));
	}

	local binary(s:%, t:%, f:(R, R) -> R):% == {
		import from I, Partial R;
		(cs, us) := constant(rs := rep s);
		(ct, ut) := constant(rt := rep t);
		cs < 0 or ct < 0 => sequence stream(0,(m:I):R +-> f(rs.m,rt.m));
		sequence stream(0, (m:I):R +-> f(rs.m, rt.m),
				max(cs, ct), f(retract us, retract ut));
	}

	(s:%) + (t:%):% == {
		zero? s => t;
		zero? t => s;
		binary(s, t, +$R);
	}

	(s:%) - (t:%):% == {
		zero? s => -t;
		zero? t => s;
		binary(s, t, -$R);
	}

	(s:%) * (t:%):% == {
		zero? s or zero? t => 0;
		binary(s, t, *$R);
	}

	(r:R) * (t:%):% == {
		zero? r => 0;
		one? r => t;
		map((x:R):R +-> r * x) t;
	}

	(s:%)^(n:I):% == {
		zero? s or one? n => s;
		zero? n => 1;
		map((x:R):R +-> x^n) s;
	}

	extree(s:%):TREE == {
		import from I, R, List TREE;
		ExpressionTreeList [extree(s.i) for i in 0..prev(#s)];
	}
}

