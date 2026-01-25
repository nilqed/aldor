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
---------------------------- sal_string.as ----------------------------------
--
-- This file defines 0-indexed null-terminated strings.
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro {
	Ch == Character;
	Z  == MachineInteger;
}

#if ALDOC
\thistype{String}
\History{Manuel Bronstein}{4/10/98}{created}
\Usage{import from \this}
\Descr{\this~provides basic strings, null--terminated,
$0$-indexed and without bound checking.}
\begin{exports}
\category{\astype{BoundedFiniteLinearStructureType} \astype{Character}}\\
\asexp{$+$}: & (\%, \%) $\to$ \% & concatenation\\
\asexp{char}: & \% $\to$ \astype{Character} & first character\\
\asexp{coerce}: & \astype{Character} $\to$ \% & conversion to a string\\
\asexp{coerce}:
& \% $\to$ \astype{TextReader} & conversion to a text input stream\\
\asexp{coerce}:
& \% $\to$ \astype{TextWriter} & conversion to a text output stream\\
\asexp{error}: & \% $\to$ \builtin{Exit} & error exit\\
\asexp{new}: & \astype{MachineInteger} $\to$ \% & buffer allocation\\
\asexp{pointer}: & \% $\to$ \astype{Pointer} &
conversion to a null--terminated C--string\\
\asexp{string}: & \astype{Pointer} $\to$ \% &
conversion from a null--terminated C--string\\
\end{exports}
#endif

String: BoundedFiniteLinearStructureType Ch with {
	+: (%, %) -> %;
#if ALDOC
\aspage{$+$}
\Usage{s \name~t}
\Signature{(\%, \%)}{\%}
\Params{ {\em s,t} & \% & strings\\ }
\Retval{$s \name t$ returns the string $s t$. Copies all the characters
of $s$ and $t$, so $s$ is unchanged after the call, and $s$ and $t$ do
not share characters with $s + t$.}
\Remarks{$s + \asfunc{LinearStructureType}{empty}$
and $\asfunc{LinearStructureType}{empty} + s$ both return
a copy of $s$.}
\begin{asex}
If $s$ is the string ``abcde'',
then $s + (s + 2)$ is the string ``abcdecde''.
\end{asex}
#endif
	char: % -> Ch;
#if ALDOC
\aspage{char}
\Usage{\name~s}
\Signature{\%}{\astype{Character}}
\Params{ {\em s} & \% & a nonempty string\\ }
\Descr{Returns the first character of s.}
#endif
	coerce: Ch -> %;
	coerce: % -> TextReader;
	coerce: % -> TextWriter;
#if ALDOC
\aspage{coerce}
\Usage{c::\%\\ s::TextReader\\ s::TextWriter}
\Signatures{
\name: & \astype{Character} $\to$ \%\\
\name: & \% $\to$ \astype{TextReader}\\
\name: & \% $\to$ \astype{TextWriter}\\
}
\Params{
{\em c} & \astype{Character} & a character\\
{\em s} & \% & a string\\
}
\Descr{c::String converts the character c to the string ``c'', while
s::T where T is an I/O stream type
converts the string s to a text reader or writer, allowing
one to read data or write data to it.}
\Remarks{When writing to a string, you must ensure that the string is
large enough for all the data that will be written to it, since the
string will not be extended and this function does not protect you against
overwriting. When reading from or writing to a string, each coercion to
a reader or writer resets the stream to the beginning of the string,
and the string is not side--affected by the subsequent read or write
operations, while the stream is side--affected.
Thus, when reading several values from the same string, you must assign
the reader to a variable and read the values from that variable,
as in the example below.}
\begin{asex}
\begin{ttyout}
import from MachineInteger, String;
s := "  12  56";
a:MachineInteger := << s::TextReader;
b:MachineInteger := << s::TextReader;
\end{ttyout}
assigns the value 12 to both a and b, while
\begin{ttyout}
import from MachineInteger, String;
s := "  12  56";
p := s::TextReader;
a:MachineInteger := << p;
b:MachineInteger := << p;
\end{ttyout}
assigns 12 to a and 56 to b.
\end{asex}
\seealso{PrimitiveMemoryBlock}{coerce}
#endif
	error: % -> Exit;
#if ALDOC
\aspage{error}
\Usage{\name~s}
\Signature{\%}{\builtin{Exit}}
\Params{ {\em s} & \% & a string\\ }
\Descr{Writes the message s to \asfunc{TextWriter}{stderr} and exits.}
#endif
	new: Z -> %;
#if ALDOC
\aspage{new}
\Usage{\name~n}
\Signature{\astype{MachineInteger}}{\%}
\Params{ {\em n} & \astype{MachineInteger} & a nonnegative size\\ }
\Retval{Returns a string of $n+1$ null characters. This is useful when
creating a memory buffer of a specified number of bytes, or when creating
a string to be used as an \astype{TextWriter}.}
#endif
	pointer: % -> Pointer;
	string: Pointer -> %;
#if ALDOC 
\aspage{pointer,string}
\astarget{pointer}
\astarget{string}
\Usage{pointer~s\\ string~p}
\Signatures{
pointer: & \% $\to$ \astype{Pointer}\\
string: & \astype{Pointer} $\to$ \%\\
}
\Params{ 
{\em s} & \% & A \salli string\\
{\em p} & \astype{Pointer} & A null--terminated C--string\\
}
\Descr{Use those functions to safely convert between null--terminated
returned or needed by C--functions
and \salli strings. Those functions have no effect
in the release version of \salli, but they are
necessary when using the debug version, so it is recommended to use
them in all cases. The C--type {\tt char*} should be replaced
by \astype{Pointer} in the prototypes
when using C--functions in \salli clients.}
#endif
	string: Literal -> %;
} == add {
	Rep == PrimitiveMemoryBlock;

	pointer(s:%):Pointer		== { import from Rep; pointer rep s; }
	free!(x:%):()			== { import from Rep; free! rep x; }
	apply(x:%, n:Z):Ch		== { import from Rep,Byte;rep(x).n::Ch;}
	(x:%) + (n:Z):%			== { import from Rep; per(rep x + n); }
	coerce(s:%):TextReader		== textReader getc! s;
	coerce(s:%):TextWriter		== textWriter putc! s;
	new(n:Z):%			== { import from Ch; new(n, null); }
	coerce(c:Ch):%			== { import from Z; new(1, c); }
	empty:%				== { import from Z; new 0; }
	empty?(s:%):Boolean		== { import from Z; zero? #s; }
	firstIndex:Z			== 0;
	local quote:Ch			== char "_"";
	string(l:Literal):%		== string(l pretend Pointer);

	set!(x:%, n:Z, y:Ch):Ch	 == {
		import from Rep, Byte;
		rep(x).n := y::Byte;
		y;
	}

	char(x:%):Ch == {
		import from Z, Boolean;
		assert(~empty? x);
		x.0;
	}

	find(t:Ch, a:%):(%, Z) == {
		for n in 0..prev(#a) repeat { a.n = t => return(a + n, n); }
		(empty, -1);
	}

	bracket(g:Generator Ch):% == {
		import from Z, List Ch;
		l:List Ch := [g];
		zero?(n := #l) => empty;
		s:% := new n;
		i:Z := 0;
		for c in l repeat {
			s.i := c;
			i := next i;
		}
		s;
	}

	map!(f:Ch -> Ch)(s:%):% == {
		import from Z;
		zero?(n := #s) => empty;
		for i in 0..prev n repeat s.i := f(s.i);
		s;
	}

	map(f:Ch -> Ch)(s:%):% == {
		import from Z;
		zero?(n := #s) => empty;
		t:% := new n;
		for i in 0..prev n repeat t.i := f(s.i);
		t;
	}

	copy!(t:%, s:%):% == {
		import from Boolean, Z;
		tooSmall? := (n := #s) > #t;
		if tooSmall? then t := new n;
		for i in 0..prev n repeat t.i := s.i;
		if ~tooSmall? then t.n := null;
		t;
	}

	copy(s:%):% == {
		import from Z;
		zero?(n := #s) => empty;
		t:% := new n;
		for i in 0..prev n repeat t.i := s.i;
		t;
	}

	error(a:%):Exit == {
		import from TextWriter, Ch, Z, Machine;
		stderr << a << newline;
		halt 0;
	}

	<< (p:BinaryReader):% == {
		import from Z, Ch;
		n:Z := << p;				-- read size first
		s:% := new n;
		for m in 0..prev n repeat s.m := << p;
		s;
	}

	bracket(t:Tuple Ch):% == {
		import from Z;
		zero?(n := length t) => empty;
		s := new n;
		for i in 0..prev n repeat s.i := element(t, next i);
		s;
	}

	(s:%) + (t:%):% == {
		import from Z;
		a := new(#s + #t);
		n:Z := 0;
		for c in s repeat { a.n := c; n := next n; }
		for c in t repeat { a.n := c; n := next n; }
		a;
	}

	new(n:Z, x:Ch):% == {
		import from Rep, Byte;
		assert(n >= 0);
		s := per new(next n, x::Byte);
		s.n := null;
		s;
	}

#if DEBUG
	string(p:Pointer):% == {
		import from Rep, Boolean, Ch, Z, Machine;
		import { ArrElt: (Arr, SInt) -> Char } from Builtin;
		n:Z := 0;
		s := p pretend Arr;
		while ~zero?(ord(ArrElt(s, n::SInt)::Ch)) repeat n := next n;
		per array(p, next n);
	}
#else
	-- actual size is irrelevant
	string(p:Pointer):% == { import from Rep; per array(p, 0); }
#endif

	generator(a:%):Generator Ch == generate {
		import from Boolean, Ch, Z;
		for n in 0.. while ~zero?(ord(c := a.n)) repeat yield c;
	}

	local putc!(s:%):Ch -> () == {
		import from Z;
		i:Z := 0;
		(c:Ch):() +-> { s.i := c; free i := next i; }
	}

	-- Text-mode scanning, send eof on a null-character
	local getc!(s:%):(() -> Ch, Ch -> ()) == {
		import from Boolean, Z;
		i:Z := 0;
		(():Ch +-> {
			zero? ord(c := s.i) => eof;
			free i := next i;
			c;
		}, (c:Ch):() +-> {
			if ~(zero? i or c = eof) then {
				free i := prev i;
				s.i := c;
			}
		})
	}

	#(s:%):Z == {
		import from Boolean, Ch;
		n:Z := 0;
		while ~zero?(ord(s.n)) repeat n := next n;
		n;
	}

	(a:%) = (b:%):Boolean == {
		import from Z, Ch;
		(na := #a) ~= #b => false;
		for n in 0..prev na repeat {
			a.n ~= b.n => return false;
		}
		true;
	}

	(p:TextWriter) << (s:%):TextWriter == {
		import from Ch;
		for c in s repeat p << c;
		p;
	}

	-- strings must be either quoted, in which case they contain any char,
	-- or chains of letters and digits (no punctuation or special chars)
	<< (p:TextReader):% == {
		import from Z, Ch, List Ch;
		local c:Ch;
		while space?(c := << p) repeat {};
		l := { c = quote => quotedString p; unquotedString(p, c) }
		s:% := new(n := #l);
		for cc in l for i in prev(n).. by -1 repeat s.i := cc;
		free! l;
		s;
	}

	-- opening quote has been read
	local quotedString(p:TextReader):List Ch == {
		import from Boolean, Ch;
		local c:Ch;
		l:List Ch := empty;
		c := << p;
		while c ~= quote repeat {
			l := cons(c, l);
			c := << p;
		}
		l;
	}

	-- first char has been read (in c), string is not quoted
	local unquotedString(p:TextReader, c:Ch):List Ch == {
		l:List Ch := empty;
		while letter? c or digit? c repeat {
			l := cons(c, l);
			c := << p;
		}
		c = newline => cons(c, l);
		push!(c, p);
		l;
	}
}
