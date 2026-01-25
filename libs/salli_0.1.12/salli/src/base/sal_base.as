-- ======================================================================
-- Copyright (C) 1991-1998, The Numerical Algorithms Group Ltd.
-- All rights reserved.
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
--
-- * Redistributions of source code must retain the above copyright
--  notice, this list of conditions and the following disclaimer.
--
-- * Redistributions in binary form must reproduce the above copyright
--  notice, this list of conditions and the following disclaimer in
--  the documentation and/or other materials provided with the
--  distribution.
--
-- * Neither the name of The Numerical Algorithms Group Ltd. nor the
--  names of its contributors may be used to endorse or promote products
--  derived from this software without specific prior written permission.
--
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
-- IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
-- TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
-- PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
-- OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
-- EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
-- PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
-- PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
-- LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
-- NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
-- SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
-- ======================================================================
-- 
------------------------------ sal_base.as -----------------------------------
--
-- This file defines basic types, whose export are limited to wrapping
-- the built-in FOAM operations. Clients of those types should not have to
-- use the Machine type. Those types should be extended later.
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#assert DontImportFromBoolean
#include "salli"

import from Machine;

#if ALDOC
\thistype{PrimitiveType}
\History{Manuel Bronstein}{28/9/98}{created}
\Usage{\this: Category}
\Descr{\this~is the category of the most basic types.}
\begin{exports}
\asexp{$=$}: & (\%, \%) $\to$ \astype{Boolean} & equality test\\
\asexp{$\tilde{}=$}: & (\%, \%) $\to$ \astype{Boolean} & inequality test\\
\end{exports}
#endif

define PrimitiveType: Category == with {
	=: (%, %) -> Boolean;
	~=: (%, %) -> Boolean;
#if ALDOC
\aspage{$=,\tilde{}=$}
\astarget{$=$}
\astarget{$\tilde{}=$}
\Usage{a = b\\ a \~{}= b}
\Signatures{
$=$: & (\%,\%) $\to$ \astype{Boolean}\\
$\tilde{}=$: & (\%,\%) $\to$ \astype{Boolean}\\
}
\Params{ {\em a, b} & \% & elements of the type\\ }
\Retval{ If $a = b$ returns \true, then $a$ and $b$ are guaranteed to
represent the same element of the type. The behavior if $a = b$ returns
\false~depends on the type, since a full equality test might not be
available. At least, it is guaranteed that $a$ and $b$ do not share the
same memory location in that case. The semantics of $a~\tilde{}=b$ is
the boolean negation of $a = b$.}
#endif
	default { (a:%) ~= (b:%):Boolean == ~(a = b); }
}

+++ Union(T) is the disjoint union type former.
+++ Union values are not mutable.
+++
+++ Author: NAG Ltd.
+++
+++ Overview: Basic
-- The 'export from Boolean' is needed so that 'u case foo' compiles ok
Union(T: Tuple Type): with { export from Boolean } == add;

+++ The Boolean data type supports logical operations.
+++ Both arguments of the binary operations are always evaluated.
+++ The Boolean type is "magic" for the compiler which expects 
+++ Boolean values for such things as if statements.
Boolean: PrimitiveType with {
	~: % -> %;
	coerce: Bool -> %;
	coerce: % -> Bool;
	false:%;
	true:%;
} == add {
	Rep == Bool;

	coerce(b:%):Bool	== rep b;
	coerce(b:Bool):%	== per b;
	false:%			== false@Bool :: %;
	true:%			== true@Bool :: %;
	~(x:%):%		== (~(x::Bool))::%;
	(a:%) = (b:%):%		== (rep a = rep b)::%;

	-- THOSE ARE BETTER THAN THE CORRESPONDING CATEGORY DEFAULTS
	(a:%) ~= (b:%):%	== (rep a ~= rep b)::%;
}

+++ MachineInteger implements machine full-word integers.
MachineInteger: PrimitiveType with {
	0:		%;
	1:		%;
	bytes:		MachineInteger;
	coerce:		SInt -> %;
	coerce:		% -> SInt;
        integer:	Literal -> %;
	min:		%;
	max:		%;
	odd?:		% -> Boolean;
	zero?:		% -> Boolean;
} == add {
	Rep == SInt;

	0:%			== per 0;
	1:%			== per 1;
	coerce(n:%):SInt	== rep n;
	coerce(n:SInt):%	== per n;
	min:%			== per min;
	max:%			== per max;
	integer(l: Literal):%	== per convert(l pretend Arr);
	odd?(n:%):Boolean	== odd?(rep n)::Boolean;
	zero?(n:%):Boolean	== zero?(rep n)::Boolean;
	(a:%) = (b:%):Boolean	== (rep a = rep b)::Boolean;

	-- THOSE ARE BETTER THAN THE CORRESPONDING CATEGORY DEFAULTS
	(a:%) ~= (b:%):Boolean	== (rep a ~= rep b)::Boolean;

	bytes:MachineInteger == {
		import from Boolean;
		m:SInt := max;
		a:% := 2147483647;
		assert((rep a <= m)::Boolean);
		m::% = a => 4;
		8;
	}
}

+++ AldorInteger implements software integers.
AldorInteger: PrimitiveType with {
	coerce:		BInt -> %;
	coerce:		% -> BInt;
} == add {
	Rep == BInt;

	(a:%) = (b:%):Boolean	== (rep a = rep b)::Boolean;
	coerce(n:%):BInt	== rep n;
	coerce(n:BInt):%	== per n;

	-- THOSE ARE BETTER THAN THE CORRESPONDING CATEGORY DEFAULTS
	(a:%) ~= (b:%):Boolean	== (rep a ~= rep b)::Boolean;
}

+++ Characters for natural language text.
+++ In the portable byte code files, characters are represented in ASCII.
+++ In a running program, characters are represented according to the
+++ machine's native character set, e.g. ASCII or EBCDIC.
Character: PrimitiveType with {
	char:	MachineInteger -> %;
	coerce:	% -> Char;
	coerce: Char -> %;
	digit?:	% -> Boolean;
	eof:	%;
	letter?:% -> Boolean;
	lower:	% -> %;
	newline:%;
	null:	%;
	ord:	% -> MachineInteger;
	space:	%;
	space?:	% -> Boolean;
	tab:	%;
	upper:	% -> %;
} == add {
	macro Z == MachineInteger;
	Rep == Char;

	-- TEMPORARY: REALLY NEEDS C-int
	-- import { EOF: CInteger} from Foreign C;
	import { EOF: MachineInteger} from Foreign C;

	coerce(c:%):Char	== rep c;
	coerce(c:Char):%	== per c;
	ord(c:%):Z		== ord(rep c)::Z;
	char(i:Z):%		== per char(i::SInt);
	newline:%		== per newline;
	space:%			== per space;
	-- TEMPORARY: REALLY NEEDS C-int
	-- eof:%			== char EOF;
	eof:%			== per char(-1@SInt);
	null:%			== char 0;
	tab:%			== char 9;
	digit?(c:%):Boolean	== digit?(rep c)::Boolean;
	letter?(c:%):Boolean	== letter?(rep c)::Boolean;
	space?(c:%):Boolean	== c = space or c = tab;
	lower(c:%):%		== per lower rep c;
	upper(c:%):%		== per upper rep c;
	(a:%) = (b:%):Boolean	== (rep a = rep b)::Boolean;

	-- THOSE ARE BETTER THAN THE CORRESPONDING CATEGORY DEFAULTS
	(a:%) ~= (b:%):Boolean	== (rep a ~= rep b)::Boolean;
}

+++ Bytes, mostly for I/O to binary streams
Byte: PrimitiveType with {
	coerce: % -> XByte;
	coerce: XByte -> %;
	coerce: % -> MachineInteger;
	coerce: Character -> %;
	coerce: % -> Character;
	eof:	%;
	lowByte: MachineInteger -> %;
} == add {
	macro Z == MachineInteger;
	Rep == XByte;

	coerce(b:%):XByte	== rep b;
	coerce(b:XByte):%	== per b;
	coerce(c:Character):%	== lowByte ord c;
	coerce(n:%):Character	== char(n::Z);
	lowByte(n:Z):%		== per convert(n::SInt);
	(a:%) = (b:%):Boolean	== { import from Z; (a::Z) = (b::Z); }
	eof:%			== (eof$Character) :: %;

	-- TEMPORARY: XByte ARE SIGNED IN Machine (BUG 1237)
	-- coerce(n:%):Z		== convert(rep n)@SInt :: Z;
	coerce(n:%):Z == {
		import from Boolean;
		m := convert(rep n)@SInt;
		negative?(m)::Boolean => (m + 256::SInt) :: Z;
		m::Z;
	}

	-- THOSE ARE BETTER THAN THE CORRESPONDING CATEGORY DEFAULTS
	(a:%) ~= (b:%):Boolean	== { import from Z; (a::Z) ~= (b::Z); }
}

+++ Pointer is the type of pointers to opaque objects.
Pointer:  PrimitiveType with {
	coerce:	 % -> MachineInteger;
	coerce:	 MachineInteger -> %;
        nil:     %;
        nil?:    % -> Boolean;
} == add {
	macro Z == MachineInteger;
        Rep == Ptr;
	coerce(p:%):Z		== convert(rep p)@SInt ::MachineInteger;
	coerce(n:Z):%		== per convert(n::SInt);
        nil:%			== per nil;
        nil?(p:%):Boolean	== nil?(rep p)::Boolean;
	(a:%) = (b:%):Boolean	== (rep a = rep b)::Boolean;

	-- THOSE ARE BETTER THAN THE CORRESPONDING CATEGORY DEFAULTS
	(a:%) ~= (b:%):Boolean	== (rep a ~= rep b)::Boolean;
}

+++ `Tuple(T)' provides functions for values of type `Tuple T'.
extend Tuple(T: Type): with {
	element: (%, MachineInteger) -> T;
	dispose!: % -> ();
	length: % -> MachineInteger;
	tuple: (MachineInteger, Pointer) -> %;
} == add {
	macro Z == MachineInteger;
	Rep == Record(size: SInt, values: Arr);

	import from Rep, Machine, Z;

	tuple(n:Z, v:Pointer):%	== per [n::SInt, v pretend Arr];
	length(t:%):Z		== rep(t).size::Z;
	element(t:%, i:Z):T	== get(T)(rep(t).values, prev(i::SInt));

	dispose!(t:%):() == {
		dispose! rep(t).values;
		dispose! rep(t);
	}
}
