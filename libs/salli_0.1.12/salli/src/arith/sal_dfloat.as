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
---------------------------- sal_dfloat.as ------------------------------------
--
-- Double precision machine floats
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro Z == MachineInteger;

#if ALDOC
\thistype{DoubleFloat}
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

DoubleFloat: Join(CopyableType, FloatType) with {
	^: (%, %) -> %;
#if ALDOC
\aspage{$\hat{}$}
\Usage{$x$ \^{} $y$}
\Signature{(\%,\%)}{\%}
\Params{ {\em x,y} & \% & floats\\ }
\Retval{Returns $x$ to the power $y$.}
#endif
	coerce: % -> DFlo$Machine;
	coerce: DFlo$Machine -> %;
	max: %;
	min: %;
#if ALDOC
\aspage{max,min}
\astarget{max}
\astarget{min}
\Usage{max\\min}
\Signature{}{\%}
\Retval{max and min return respectively the largest and the smallest
double--precision machine floats.}
#endif
} == add {
	import from Machine;
	-- TEMPORARY: DFlo MUST BE BOXED IN 1.1.12 OR THEY CRASH AT RUNTIME
	-- Rep == DFlo;
	-- macro pper == per;
	-- macro prep == rep;
	Rep == Record(float:DFlo);
	macro pper x == per [x];
	macro prep x == rep(x).float;
	import from Rep;

	coerce(x:%):DFlo			== prep x;
	coerce(x:DFlo):%			== pper x;
	0:%					== pper 0;
	1:%					== pper 1;
	min:%					== pper min;
	max:%					== pper max;
	(a:%) + (b:%):%				== pper(prep a + prep b);
	(a:%) * (b:%):%				== pper(prep a * prep b);
	(a:%) = (b:%):Boolean			== (prep a = prep b)::Boolean;
	(a:%) < (b:%):Boolean			== (prep a < prep b)::Boolean;
	(a:%) ^ (b:Z):%				== a ^ (b::%);
	coerce(a:Z):%				== pper convert(a::SInt);
	float(l:Literal):%			== pper convert(l pretend Arr);
	fraction(a:%):%				== pper fraction prep a;
	local minus:Character			== { import from Z; char 45; }
	copy(a:%):%				== a;
	local five:%				== { import from Z; 5::% }
	truncate(a:%):AldorInteger	== truncate(prep a)::AldorInteger;

	-- THOSE ARE BETTER THAN THE CORRESPONDING CATEGORY DEFAULTS
	(a:%) ~= (b:%):Boolean			== (prep a ~= prep b)::Boolean;
	(a:%) <= (b:%):Boolean			== (prep a <= prep b)::Boolean;
	zero?(a:%):Boolean			== zero?(prep a)::Boolean;
	(a:%) - (b:%):%				== pper(prep a - prep b);
	-(a:%):%				== pper(- prep a);
	add!(a:%, b:%):%			== { zero? a => copy b; a + b; }
	times!(a:%, b:%):%			== { one? a => copy b; a * b; }
	next(a:%):%				== pper(next prep a);
	prev(a:%):%				== pper(prev prep a);

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
		pper(prep a / prep b);
	}

	(a:%) ^ (b:%):%	== {
		import { pow: (%, %) -> % } from Foreign C;
		pow(a, b);
	}

	-- TEMPORARY: FIX FOR 64-BIT dissemble-bug in Machine (1.1.12p6)
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
	local mydissemble(x:DFlo):(Bool, SInt, Word, Word) == {
		(s, e, m1, m2) := dissemble x;
		(patch(s pretend SInt) pretend Bool, patch e, m1, m2);
	}

	(p:BinaryWriter) << (x:%):BinaryWriter == {
		import from Boolean, Z;
		(s, e, m1, m2) := mydissemble prep x;
		p := p << s::Boolean << e::Z
			<< (m1 pretend SInt)::Z << (m2 pretend SInt)::Z;
	}

	<< (p:BinaryReader):% == {
		s:Boolean := << p;
		e:Z := << p;
		m1:Z := << p;
		m2:Z := << p;
		pper assemble(s::Bool, e::SInt, (m1::SInt) pretend Word,
						(m2::SInt) pretend Word);
	}

	(p:TextWriter) << (b:%):TextWriter == {
		import from Boolean, Z, AldorInteger, FloatTypeTools %;
		zero? b => p << 0@Z;
		b < 0 => p << minus << -b;
		assert(b > 0);
		(s, e, m1, m2) := mydissemble prep b;
		x := pper assemble(s, 0, m1, m2);
		assert(x >= 1); assert(x < 2.0);
		l := e::Z::%;
		-- b = x 2^l  1 <= x < 2   =   y 10^k  1 <= y < 10
		z := (x-1.5)*0.289529654602168 + 0.1760912590558
							+ l*0.301029995663981;
		k := convert(truncate prep z)@SInt :: Z;
		if z < 0 and k::% > z then k := prev k;
		y := pper assemble(s, (e::Z - k)::SInt, m1, m2);
		-- do not use exponentiation from % since it is not
		-- supported in the interactive loop (external C function)
		import from BinaryPowering(%, Z);
		if k < 0 then y := y * binaryExponentiation(five, -k);
		else if k > 0 then y := y / binaryExponentiation(five, k);
		print(y, k, 17, p);
	}
}
