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
---------------------------- sal_int.as ------------------------------------
--
-- Aldor software integers
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro {
	Z == MachineInteger;
	B == BInt;
}

#if ALDOC
\thistype{AldorInteger}
\History{Manuel Bronstein}{7/10/98}{created}
\Usage{import from \this}
\Descr{\this~provides an interface to the software (``infinite'' precision)
integers provided by the \aldor virtual machine.}
\begin{exports}
\category{\astype{IntegerType}}\\
\end{exports}
#endif

extend AldorInteger: IntegerType with { export from IntegerSegment % } == add {
	import from Machine;

	0:%					== 0@B :: %;
	1:%					== 1@B :: %;
	(a:%) + (b:%):%				== (a::B + b::B)::%;
	(a:%) * (b:%):%				== (a::B * b::B)::%;
	(a:%) < (b:%):Boolean			== (a::B < b::B)::Boolean;
	(a:%) quo (b:%):%			== (a::B quo b::B)::%;
	(a:%) rem (b:%):%			== (a::B rem b::B)::%;
	coerce(a:Z):%				== convert(a::SInt)@B :: %;
	machine(a:%):Z				== convert(a::B)@SInt :: Z;
	integer(l: Literal):%			== convert(l pretend Arr)@B ::%;
	length(a:%):Z				== length(a::B)::Z;
	even?(a:%):Boolean			== even?(a::B)::Boolean;
	gcd(a:%, b:%):%				== gcd(a::B, b::B)::%;
	bit?(a:%, b:Z):Boolean			== bit(a::B, b::SInt)::Boolean;

	-- THOSE ARE BETTER THAN THE CORRESPONDING CATEGORY DEFAULTS
	(a:%) <= (b:%):Boolean			== (a::B <= b::B)::Boolean;
	zero?(a:%):Boolean			== zero?(a::B)::Boolean;
	(a:%) - (b:%):%				== (a::B - b::B)::%;
	-(a:%):%				== (-(a::B))::%;
	add!(a:%, b:%):%			== a + b;	-- not copyable
	times!(a:%, b:%):%			== a * b;	-- not copyable
	next(a:%):%				== next(a::B)::%;
	prev(a:%):%				== prev(a::B)::%;
	odd?(a:%):Boolean			== odd?(a::B)::Boolean;

	-- TEMPORARY (BUG1182) DEFAULTS DON'T INLINE WELL
	xor(a:%, b:%):% == (a /\ ~b) \/ (~a /\ b);
	(a:%) > (b:%):Boolean == ~(a <= b);
	(a:%) >= (b:%):Boolean == ~(a < b);
	max(a:%, b:%):% == { a < b => b; a };
	min(a:%, b:%):% == { a < b => a; b };
	minus!(a:%):% == - a;
	minus!(a:%, b:%):% == a - b;
	one?(a:%):Boolean == a = 1;
	abs(a:%):% == { a < 0 => -a; a }
	set(a:%, n:Z):% == a \/ shift(1, n);
	clear(a:%, n:Z):% == a /\ ~(shift(1, n));
	hash(a:%):Z == machine a;
	(a:%) mod (b:%):% == {
		assert(b ~= 0);
		(r := a rem b) < 0 => r + abs b;
		r;
	}

	sign(a:%):Z == {
		zero? a => 0;
		a > 0 => 1;
		-1;
	}

	(a:%) ^ (b:Z):%	== {
		import from BinaryPowering(%, Z);
		binaryExponentiation(a, b);
	}

	divide(a:%, b:%):(%, %)	== {
		(q, r) := divide(a::B, b::B);
		(q::%, r::%);
	}

	random():% == {
		import from RandomNumberGenerator;
		randomInteger()::%;
	}

	random(n:Z):% == {
		import from RandomNumberGenerator;
		assert(n > 0);
		r:% := 0;
		m := 8 * bytes$Z;
		for i in 1..n repeat
			r := add!(shift!(r, m), randomInteger()::%);
		r;
	}

	shift(a:%, b:Z):% == {
		b < 0 => shiftDown(a::B, (-b)::SInt)::%;
		shiftUp(a::B, b::SInt)::%;
	}

	nthRoot(x:%, e:%):(Boolean, %) == {
		import from IntegerTypeTools %;
		binaryNthRoot(x, e);
	}

	(p:TextWriter) << (x:%):TextWriter == {
		import from IntegerTypeTools %;
		print(x, 10@%, p);
	}

	<< (p:TextReader):% == {
		import from IntegerTypeTools %;
		scan p;
	}

	~(a:%):% == {
		import from Boolean, Z;
		b:% := 0;
		for n in prev(length a)..0 by -1 repeat {
			b := shift(b, 1);
			if ~bit?(a, n) then b := next b;
		}
		b;
	}

	(a:%) \/ (b:%):% == {
		import from Boolean, Z;
		if length a < length b then (a, b) := (b, a);
		c:% := 0;
		for n in prev(length a)..0 by -1 repeat {
			c := shift(c, 1);
			if bit?(a, n) or bit?(b, n) then c := next c;
		}
		c;
	}

	(a:%) /\ (b:%):% == {
		import from Boolean, Z;
		if length a > length b then (a, b) := (b, a);
		c:% := 0;
		for n in prev(length a)..0 by -1 repeat {
			c := shift(c, 1);
			if bit?(a, n) and bit?(b, n) then c := next c;
		}
		c;
	}

	-- integers are written in binary low byte first
	-- the length is in bytes
	(p:BinaryWriter) << (x:%):BinaryWriter == {
		import from Boolean, Z, Byte;
		p := p << (sgn := sign x);		-- write sign first
		zero? sgn => p;
		(s, r) := divide(length x, 8);
		if ~zero? r then s := next s;
		p := p << s;				-- write size
		for m in 1..s repeat {			-- must send s bytes
			-- TEMPORARY: BECAUSE OF BUG1191,
			-- x /\ 255 REALLY MEANS |x| /\ 255
			p := p << lowByte machine(x /\ 255);
			-- QUADRATIC SPACE, NO ACCESS TO THE LIMBS
			x := shift(x, -8);
		}
		p;
	}

	-- integers are written in binary low byte first
	-- the length is in bytes
	<< (p:BinaryReader):% == {
		import from Z, Byte;
		sgn:Z := << p;				-- scan sign first
		zero? sgn => 0;
		s:Z := << p;				-- read size
		x:% := 0;
		st:Z := 0;
		b := lowByte st;
		for m in 1..s repeat {			-- must read s bytes
			-- QUADRATIC SPACE, NO ACCESS TO THE LIMBS
			b := << p;
			x := x \/ shift(b::Z::%, st);
			st := st + 8;
		}
		sgn < 0 => -x;
		x;
	}
}
