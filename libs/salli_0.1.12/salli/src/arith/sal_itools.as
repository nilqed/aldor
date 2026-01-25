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
---------------------------- sal_itools.as -------------------------------
--
-- This file provides undocumented tools for integer-like types
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro Z == MachineInteger;

-- internal type giving common implementations to concrete IntegerType's
IntegerTypeTools(T:IntegerType): with {
	binaryNthRoot: (T, T) -> (Boolean, T);
	print: (T, T, TextWriter) -> TextWriter;	-- second arg is base
	scan: TextReader -> T;
	scan: (TextReader, T, T) -> T;			-- second arg is base
} == add {
	local plus:Character	== { import from Z; char 43; }
	local minus:Character	== { import from Z; char 45; }

	binaryNthRoot(x:T, e:T):(Boolean, T) == {
		zero? x or one? x => (true, x);
		x < 0 => {
			assert(odd? e);
			(found?, s) := binaryNthRoot(-x, e);
			(found?, { found? => -s; prev(-s) });
		}
		assert(x > 1);
		ee := machine e;
		import from BinarySearch(T, T);
		binarySearch(x, (s:T):T +-> s^ee, 1, x quo e);
	}

	scan(p:TextReader):T == {
		local c:Character;
		while space?(c := << p) repeat {};
		c = plus => read p;
		c = minus => - read p;
		digit? c => scan(p, 10::T, value c);
		0;
	}

	-- the sign (+/-) has been read, spaces are allowed
	local read(p:TextReader):T == {
		local c:Character;
		while space?(c := << p) repeat {};
		digit? c => scan(p, 10::T, value c);
		0;
	}

	-- the sign (+/-) and first digit have been read, no spaces allowed
	-- n = value already read
	scan(p:TextReader, base:T, n:T):T == {
		local c:Character;
		while digit?(c := << p, base) repeat n := base * n + value c;
		push!(c, p);
		n;
	}

	local value(c:Character):T == {
		import from Z;
		digit? c => ord(c)::T - 48::T;
		ord(c)::T - 87::T;
	}

	local digit?(c:Character, base:T):Boolean == {
		import from Z;
		digit? c => true;
		n := ord(c)::T - 87::T;
		n > 9 and n < base;
	}

	local digit(x:T):Character == {
		assert(x >= 0);
		x < 10::T => char machine(x + 48::T);
		char machine(x + 87::T);
	}

	print(x:T, base:T, p:TextWriter):TextWriter == {
		macro REC == Record(digit:Character, next:Pointer);
		import from Boolean, Character, Pointer, REC;
		zero? x => p << char 48;
		if x < 0 then {
			p := p << minus;
			x := -x;
		}
		l := nil;
		while x > 0 repeat {
			(x, r) := divide(x, base);
			l := ([digit r, l]$REC) pretend Pointer;
		}
		while ~nil? l repeat {
			p := p << (l pretend REC).digit;
			l := (l pretend REC).next;
		}
		p;
	}
}

