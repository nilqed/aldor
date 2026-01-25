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
---------------------------- sal_barray.as ----------------------------------
--
-- This file defines primitive memory blocks, i.e. packed byte-arrays
-- Those arrays are 0-indexed and do not do bound-checking.
--
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro Z == MachineInteger;

#if ALDOC
\thistype{PrimitiveMemoryBlock}
\History{Manuel Bronstein}{24/5/2000}{created}
\Usage{import from \this}
\Descr{\this~provides packed arrays of bytes,
$0$-indexed and without bound checking (the debug version
of \salli provides bound--checking for primitive memory blocks).}
\begin{exports}
\category{\astype{PrimitiveArrayType} \astype{Byte}}\\
\asexp{coerce}:
& \% $\to$ \astype{BinaryReader} & conversion to a binary input stream\\
\asexp{coerce}:
& \% $\to$ \astype{BinaryWriter} & conversion to a binary output stream\\
\end{exports}
#endif

PrimitiveMemoryBlock: PrimitiveArrayType Byte with {
	coerce: % -> BinaryReader;
	coerce: % -> BinaryWriter;
#if ALDOC
\aspage{coerce}
\Usage{a::BinaryReader\\ a::BinaryWriter}
\Signatures{
\name: & \% $\to$ \astype{BinaryReader}\\
\name: & \% $\to$ \astype{BinaryWriter}\\
}
\Params{ {\em a} & \% & a primitive memory block\\ }
\Descr{a::T where T is an I/O stream type
converts the block s to a binary reader or writer, allowing
one to read data or write data to it.}
\Remarks{When writing to a memory block, you must ensure that the block is
large enough for all the data that will be written to it, since the
block will not be extended and this function does not protect you against
overwriting. When reading from or writing to a memory block, each coercion
to a reader or writer resets the stream to the beginning of the block,
and the block is not side--affected by the subsequent read or write operations,
while the stream is side--affected.
Thus, when reading several values from the same block, you must assign
the reader to a variable and read the values from that variable.}
\seealso{\asfunc{String}{coerce}}.
#endif
} == add {
	import from Machine;
#if DEBUG
	Rep == Record(sz:Z, data:Arr);
	local data(x:%):Arr	== { import from Rep; rep(x).data }
	local size(x:%):Z	== { import from Rep; rep(x).sz; }
	local arr(x:Arr, n:Z):%	== { import from Rep; per [n, x]; }
#else
	Rep == Arr;
	local data(x:%):Arr	== rep x;
	local arr(x:Arr, n:Z):%	== per x;
	local arr(x:Arr):%	== per x;
#endif

	import {
		ArrNew: (Char, SInt) -> Arr;
		ArrElt: (Arr,  SInt) -> Char;
		ArrSet: (Arr,  SInt, Char) -> Char;
	} from Builtin;

	pointer(a:%):Pointer		== int(a)::Pointer;
	empty:%				== (nil$Pointer) pretend %;
	empty?(a:%):Boolean		== nil?(a pretend Pointer)$Pointer;
	firstIndex:Z			== 0;
	coerce(s:%):BinaryReader	== binaryReader getb! s;
	coerce(s:%):BinaryWriter	== binaryWriter putb! s;

	local putb!(s:%):Byte -> () == {
		import from Z;
		i:Z := 0;
		(b:Byte):() +-> { s.i := b; free i := next i; }
	}

	-- Binary-mode scanning, never send eof, no pushback
	local getb!(s:%):() -> Byte == {
		import from Z;
		i:Z := 0;
		():Byte +-> {
			b := s.i;
			free i := next i;
			b;
		}
	}

	free!(x:%):() == {
		import from Boolean;
		if ~empty?(x) then dispose! data x;
	}

	resize!(a:%, oldsz:Z, newsz:Z):% == {
		assert(oldsz >= 0); assert(newsz >= 0);
		newsz <= oldsz => a;
		b := new newsz;
		for i in 0..prev oldsz repeat b.i := a.i;
		free! a;
		b;
	}

	new(n:Z):% == {
		assert(n >= 0);
		import from Character;
		AGAT("pmemblocknew", n);
		arr(ArrNew(null::Char, n::SInt), n);
	}

	new(n:Z, x:Byte):% == {
		assert(n >= 0);
		import from Character;
		AGAT("pmemblocknew", n);
		c := x::Character::Char;
		a := ArrNew(c, n::SInt);
		for i in 0..prev n repeat ArrSet(a, i::SInt, c);
		arr(a, n);
	}

#if DEBUG
	array(p:Pointer, n:Z):%	== arr(p pretend Arr, n);

	apply(x:%, n:Z):Byte == {
		import from Character;
		assert(n >= 0); assert(n < size x);
		ArrElt(data x, n::SInt)::Character::Byte;
	}

	set!(x:%, n:Z, y:Byte):Byte == {
		import from Character;
		assert(n >= 0); assert(n < size x);
		ArrSet(data x, n::SInt, y::Character::Char);
		y;
	}

	(x:%) + (n:Z):% == {
		assert(0 <= n);
		p:Ptr := convert((int(x) + n)::SInt);
		arr(p pretend Arr, size(x) - n);
	}
#else
	array(p:Pointer, n:Z):%		== p pretend %;

	apply(x:%, n:Z):Byte == {
		import from Character;
		ArrElt(data x, n::SInt)::Character::Byte;
	}

	set!(x:%, n:Z, y:Byte):Byte == {
		import from Character;
		ArrSet(data x, n::SInt, y::Character::Char);
		y;
	}

	(x:%) + (n:Z):% == {
		assert(0 <= n);
		p:Ptr := convert((int(x) + n)::SInt);
		arr(p pretend Arr);
	}
#endif

	bracket(g:Generator Byte):% == {
		import from Z, List Byte;
		l:List Byte := [g];
		a:% := new(n := #l);
		for t in l for i in 0.. repeat a.i := t;
		a;
	}

	local int(a:%):Z == {
		r := data a;
		-- COMPILER BUG: convert(r)@SInt returns 0!
		-- n:SInt := convert r;
		n:SInt := r pretend SInt;
		n::Z;
	}

	bracket(t:Tuple Byte):% == {
		import from Z;
		zero?(n := length t) => empty;
		a := new n;
		for i in 0..prev n repeat a.i := element(t, next i);
		a;
	}

	equal?(a:%, b:%, n:Z):Boolean == {
		import from Byte;
		assert(0 <= n);
		-- must go by increasing indices to avoid
		-- ArrayException for unequal arrays
		for i in 0..prev n repeat a.i ~= b.i => return false;
		true;
	}
}
