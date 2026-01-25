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
---------------------------- sal_segment.as ------------------------------------
--
-- Int segments
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro {
	Ch == Character;
	I  == MachineInteger;
}

#if ALDOC
\thistype{IntegerSegment}
\History{Manuel Bronstein}{26/10/98}{created}
\Usage{import from \this~Z}
\Params{ {\em Z} & \astype{IntegerType} & an integer type\\ }
\Descr{\this(Z) implements open and closed segments of Z, \ie a selection
of equally spaced integers in a range of the form $[a,b]$ or $[a, +\infty)$.}
\begin{exports}
\category{\astype{PrimitiveType}}\\
\category{\astype{InputType}}\\
\category{\astype{OutputType}}\\
\category{\astype{SerializableType}}\\
\asexp{..}: & Z $\to$ \% & creation of a segment\\
& (Z, Z) $\to$ \% & \\
\asexp{by}: & (\%, Z) $\to$ \% & change the spacing\\
\asexp{generator}: & \% $\to$ \astype{Generator} Z & iterate over a segment\\
\asexp{high}: & \% $\to$ Z & upper bound\\
\asexp{low}: & \% $\to$ Z & lower bound\\
\asexp{open?}: & \% $\to$ \astype{Boolean} & check whether a segment is open\\
\asexp{step}: & \% $\to$ Z & spacing\\
\end{exports}
#endif

IntegerSegment(Z:IntegerType):
	Join(PrimitiveType, InputType, OutputType, SerializableType) with {
		.. : Z -> %;
		.. : (Z, Z) -> %;
#if ALDOC
\aspage{..}
\Usage{a\name\\a\name b}
\Signatures{
\name: & Z $\to$ \%\\
\name: & (Z, Z) $\to$ \%\\
}
\Params{ {\em a,b} & Z & integers\\ }
\Retval{a\name~returns the open range $[a, +\infty)$ while
a\name b returns the closed range $[a, b]$. Every integer in the range
belongs to the resulting segment.}
\seealso{\asexp{by}}
#endif
		by: (%, Z) -> %;
		step: % -> Z;
#if ALDOC
\aspage{by,step}
\astarget{by}
\astarget{step}
\Usage{s~by~n\\ step~s}
\Signatures{
by: & (\%,Z) $\to$ \%\\
step: & \% $\to$ Z\\
}
\Params{
{\em s} & \% & a segment\\
{\em n} & Z & a step\\
}
\Retval{s~by~n changes s to become the segment consisting of every
$\sth{n}$ integer in its range,
\ie the integers $a, a + n, a + 2n, \dots$ that are
within the range $[a, b]$ or $[a, +\infty)$ of s, while
step(s) returns n such that s is the segment consisting of every $\sth{n}$
integer in its range.}
\Remarks{The function s~by~n does not create a new segment but side-effects s,
whose former step is lost.}
#endif
		generator: % -> Generator Z;
#if ALDOC
\aspage{generator}
\Usage{ for x in s repeat \{ \dots \}\\ for x in \name~s repeat \{ \dots \} }
\Signature{\%}{\astype{Generator} Z}
\Params{ {\em s} & \% & a segment\\ }
\Descr{This functions allows a segment to be iterated.
This generator yields the integers of s in succession.}
\begin{asex}
The following code computes the sum of all the positive even machine integers
that are smaller than $n$:
\begin{ttyout}
evenSum(n:MachineInteger):MachineInteger == {
    s := 0;
    for x in 2..prev(n) by 2 repeat s := s + x;
    s;
}
\end{ttyout}
\end{asex}
#endif
		high: % -> Z;
		low: % -> Z;
#if ALDOC
\aspage{high,low}
\astarget{high}
\astarget{low}
\Usage{high~s\\low~s}
\Signature{\%}{Z}
\Params{ {\em s} & \% & a segment\\ }
\Retval{high(s) and low(s) return respectively the upper and lower bound of
the range of s. The result of high(s) is undefined if s is an open segment.}
#endif
		open?: % -> Boolean;
#if ALDOC
\aspage{open?}
\Usage{\name~s}
\Signature{\%}{\astype{Boolean}}
\Params{ {\em s} & \% & a segment\\ }
\Retval{Returns \true if the range of s is infinite, \false otherwise.}
#endif
} == add {
	Rep == Record(open: Boolean, low:Z, high:Z, step:Z);

	(a:Z).. :%	== { import from Boolean, Rep; per [true, a, a, 1]; }
	(a:Z)..(b:Z):%	== { import from Boolean, Rep; per [false, a, b, 1]; }
	(s:%) by (c:Z):%== { import from Rep; rep(s).step := c; s; }
	low(s:%):Z		== { import from Rep; rep(s).low; }
	high(s:%):Z		== { import from Rep; rep(s).high; }
	step(s:%):Z		== { import from Rep; rep(s).step; }
	open?(s:%):Boolean	== { import from Rep; rep(s).open; }
	local comma:Ch		== { import from I; char 44; }
	local dot:Ch		== { import from I; char 46; }
	local leftBracket:Ch	== { import from I; char 91; }
	local rightBracket:Ch	== { import from I; char 93; }

	(s:%) = (t:%):Boolean == {
		import from Z;
		open? s = open? t and low s = low t
			and high s = high t and step s = step t;
	}

	-- BUG 1182: DOES NOT INLINE WELL IF BROKEN INTO SUBFUNCTIONS
	generator(s:%):Generator Z == generate {
		import from Z;
		op? := open? s;
		a := low s;
		one?(c := step s) => {
			op? => repeat { yield a; a := next a }
			b := high s;
			while a <= b repeat { yield a; a := next a }
		}
		op? => repeat { yield a; a := a + c; }
		b := high s;
		c < 0 => while b <= a repeat { yield a; a := a + c }
		while a <= b repeat { yield a; a := a + c; }
	}

	-- prints as ..[from, to, step, open?]
	(p:TextWriter) << (s:%):TextWriter == {
		import from Z, Boolean, Character;
		p << dot << dot << leftBracket << low s << comma << high s _
		  << comma << step s << comma << open? s << rightBracket;
	}

	-- used in case of syntax error while scanning
	local bad(p:TextReader, c:Character):% == {
		import from Z;
		push!(c, p);
		0..0;
	}

	<< (p:TextReader):% == {
		import from Z, Boolean, Character, Rep;
		local c:Character;
		while space?(c := << p) repeat {}
		(c ~= dot) or (c := << p) ~= dot
			or (c := << p) ~= leftBracket => bad(p, c);
		lo:Z := << p;
		while space?(c := << p) repeat {}
		c ~= comma => bad(p, c);
		hi:Z := << p;
		while space?(c := << p) repeat {}
		c ~= comma => bad(p, c);
		st:Z := << p;
		while space?(c := << p) repeat {}
		c ~= comma => bad(p, c);
		op?:Boolean := << p;
		while space?(c := << p) repeat {}
		c ~= rightBracket => bad(p, c);
		per [op?, lo, hi, st];
	}

	(p:BinaryWriter) << (s:%):BinaryWriter == {
		import from Z, Boolean;
		p << open? s << low s << high s << step s;
	}

	<< (p:BinaryReader):% == {
		import from Boolean, Z, Rep;
		op?:Boolean := << p;
		lo:Z := << p;
		hi:Z := << p;
		st:Z := << p;
		per [op?, lo, hi, st];
	}
}
