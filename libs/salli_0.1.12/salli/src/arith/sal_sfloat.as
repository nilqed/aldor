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
---------------------------- sal_sfloat.as ------------------------------------
--
-- Single precision machine floats
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro Z == MachineInteger;

#if ALDOC
\thistype{SingleFloat}
\History{Manuel Bronstein}{26/10/98}{created}
\Usage{import from \this}
\Descr{\this~implements the single-precision signed machine floats.}
\begin{exports}
\category{\astype{CopyableType}}\\
\category{\astype{FloatType}}\\
\asexp{$\hat{}$}: & (\%, \%) $\to$ \% & exponentiation\\
\asexp{max}: & \% & largest single--precision machine float\\
\asexp{min}: & \% & smallest single--precision machine float\\
\end{exports}
#endif

SingleFloat: Join(CopyableType, FloatType) with {
	^: (%, %) -> %;
#if ALDOC
\aspage{$\hat{}$}
\Usage{$x$ \^{} $y$}
\Signature{(\%,\%)}{\%}
\Params{ {\em x,y} & \% & floats\\ }
\Retval{Returns $x$ to the power $y$.}
#endif
	coerce: % -> SFlo$Machine;
	coerce: SFlo$Machine -> %;
	max: %;
	min: %;
#if ALDOC
\aspage{max,min}
\astarget{max}
\astarget{min}
\Usage{max\\min}
\Signature{}{\%}
\Retval{max and min return respectively the largest and the smallest
single--precision machine floats.}
#endif
} == add {
	import from Machine;
	Rep == SFlo;

	coerce(x:%):SFlo			== rep x;
	coerce(x:SFlo):%			== per x;
	0:%					== per 0;
	1:%					== per 1;
	min:%					== per min;
	max:%					== per max;
	(a:%) + (b:%):%				== per(rep a + rep b);
	(a:%) * (b:%):%				== per(rep a * rep b);
	(a:%) = (b:%):Boolean			== (rep a = rep b)::Boolean;
	(a:%) < (b:%):Boolean			== (rep a < rep b)::Boolean;
	(a:%) ^ (b:Z):%				== a ^ (b::%);
	coerce(a:Z):%				== per convert(a::SInt);
	float(l:Literal):%			== per convert(l pretend Arr);
	fraction(a:%):%				== per fraction rep a;
	local minus:Character			== { import from Z; char 45; }
	copy(a:%):%				== a;
	local five:%				== { import from Z; 5::% }
	truncate(a:%):AldorInteger	== truncate(rep a)::AldorInteger;

	-- THOSE ARE BETTER THAN THE CORRESPONDING CATEGORY DEFAULTS
	(a:%) ~= (b:%):Boolean			== (rep a ~= rep b)::Boolean;
	(a:%) <= (b:%):Boolean			== (rep a <= rep b)::Boolean;
	zero?(a:%):Boolean			== zero?(rep a)::Boolean;
	(a:%) - (b:%):%				== per(rep a - rep b);
	-(a:%):%				== per(- rep a);
	add!(a:%, b:%):%			== { zero? a => copy b; a + b; }
	times!(a:%, b:%):%			== { one? a => copy b; a * b; }
	next(a:%):%				== per(next rep a);
	prev(a:%):%				== per(prev rep a);

	-- TEMPORARY (BUG1182) DEFAULTS DON'T INLINE WELL
	(a:%) > (b:%):Boolean == ~(a <= b);
	(a:%) >= (b:%):Boolean == ~(a < b);
	max(a:%, b:%):% == { a < b => b; a };
	min(a:%, b:%):% == { a < b => a; b };
	minus!(a:%):% == - a;
	minus!(a:%, b:%):% == a - b;
	one?(a:%):Boolean == a = 1;
	abs(a:%):% == { a < 0 => -a; a }

	(a:%) / (b:%):% == {
		import from Boolean;
		assert(~zero? b);
		per(rep a / rep b);
	}

	(a:%) ^ (b:%):%	== {
		import { powf: (%, %) -> % } from Foreign C;
		powf(a, b);
	}

	-- TEMPORARY: FIX FOR 64-BIT dissemble-bug in Machine (BUG1236)
	local b64?:Boolean	== { import from Z; bytes = 8 }
	local maskneg:Z		== shift(-1, 32);
	local maskpos:Z		== 2^32 - 1;
	local patch(x:SInt):SInt == {
		b64? => {
			n := x::Z;
			bit?(n, 31) => (n \/ maskneg)::SInt;
			(n /\ maskpos)::SInt;
		}
		x;
	}
	local mydissemble(x:SFlo):(Bool, SInt, Word) == {
		(s, e, m) := dissemble x;
		(patch(s pretend SInt) pretend Bool, patch e, m);
	}

	(p:BinaryWriter) << (x:%):BinaryWriter == {
		import from Boolean, Z;
		(s, e, m) := mydissemble rep x;
		p << s::Boolean << e::Z << (m pretend SInt)::Z;
	}

	<< (p:BinaryReader):% == {
		s:Boolean := << p;
		e:Z := << p;
		m:Z := << p;
		per assemble(s::Bool, e::SInt, (m::SInt) pretend Word);
	}

	(p:TextWriter) << (b:%):TextWriter == {
		import from Boolean, Z, AldorInteger, FloatTypeTools %;
		zero? b => p << 0@Z;
		b < 0 => p << minus << -b;
		assert(b > 0);
		(s, e, m) := mydissemble rep b;
		x := per assemble(s, 0, m);
		assert(x >= 1); assert(x < 2.0);
		l := e::Z::%;
		-- b = x 2^l  1 <= x < 2   =   y 10^k  1 <= y < 10
		z := (x-1.5)*0.289529654602168 + 0.1760912590558
							+ l*0.301029995663981;
		k := convert(truncate rep z)@SInt :: Z;
		if z < 0 and k::% > z then k := prev k;
		y := per assemble(s, (e::Z - k)::SInt, m);
		-- do not use exponentiation from % since it is not
		-- supported in the interactive loop (external C function)
		import from BinaryPowering(%, Z);
		if k < 0 then y := y * binaryExponentiation(five, -k);
		else if k > 0 then y := y / binaryExponentiation(five, k);
		print(y, k, 8, p);
	}
}
