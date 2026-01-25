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
---------------------------- sal_tstream.as ---------------------------------
--
-- This file defines text read/write streams
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro {
	Ch == Character;
	Z == MachineInteger;
}

#if ALDOC
\thistype{TextReader}
\History{Manuel Bronstein}{1/10/98}{created}
\Usage{import from \this}
\Descr{\this~provides various input streams.}
\begin{exports}
\asexp{push!}: & (\astype{Character}, \%) $\to$ () & push back a character\\
\asexp{read!}: & \% $\to$ \astype{Character} & read from a stream\\
\asexp{stdin}: & \% & standard input stream\\
\asexp{textReader}: &
(() $\to$ \astype{Character}, \astype{Character} $\to$ ()) $\to$ \% &
create a stream\\
\end{exports}
#endif

TextReader: with {
	push!: (Ch, %) -> ();
#if ALDOC
\aspage{push!}
\Usage{\name(c, s)}
\Signature{(\astype{Character},\%)}{()}
\Params{
{\em c} & \astype{Character} & a character\\
{\em s} & \% & a stream\\
}
\Retval{Pushes the character $c$ back onto $s$.
One character of pushback is guaranteed, this function might
however fail if it is called too many times on the same stream
without intervening read or positionning calls.}
#endif
	read!: % -> Ch;
#if ALDOC
\aspage{read!}
\Usage{\name~s}
\Signature{\%}{\astype{Character}}
\Params{ {\em s} & \% & a stream\\ }
\Retval{Reads a character from $s$ and returns it. Returns
\asfunc{Character}{eof} if the end of file is reached.}
#endif
	stdin: %;
#if ALDOC
\aspage{stdin}
\Usage{\name}
\Signature{}{\%}
\Retval{stdin is the standard input stream.}
#endif
	textReader: (() -> Ch, Ch -> ()) -> %;
#if ALDOC
\aspage{textReader}
\Usage{\name(f, g)}
\Signature{(() $\to$ \astype{Character}, \astype{Character} $\to$ ())}{\%}
\Params{
{\em f} & () $\to$ \astype{Character} & the single--character read function\\
{\em g}& \astype{Character} $\to$ () & the single--character pushback function\\
}
\Retval{Returns the input stream for which $f()$ reads a character
and $g(c)$ pushes back the character $c$.}
#endif
} == add {
	Rep == Record(read: () -> Ch, push: Ch -> ());

	import {
		fgetc: Pointer -> Z;
		-- TEMPO: NEEDS A TYPE FOR C-int
		-- ungetc: (CInteger, Pointer) -> CInteger;
		lungetc: (Z, Pointer) -> Z;
		stdinFile: () -> Pointer;
	} from Foreign C;

	local getc(s:Pointer)():Ch	== char fgetc s;
	local pbak(s:Pointer)(c:Ch):()	== lungetc(ord c, s);
	read!(s:%):Ch			== { import from Rep; rep(s).read(); }
	push!(c:Ch, s:%):()		== { import from Rep; rep(s).push(c); }

	textReader(f:() -> Ch, g:Ch -> ()):% == {
		import from Rep;
		per [f, g];
	}

	local creader(s:Pointer):% == {
		import from Rep;
		per [getc s, pbak s];
	}

	stdin:%				== creader stdinFile();
}

#if ALDOC
\thistype{TextWriter}
\History{Manuel Bronstein}{28/9/98}{created}
\Usage{import from \this}
\Descr{\this~provides various output streams.}
\begin{exports}
\asexp{flush!}: & \% $\to$ \% & flush a stream\\
\asexp{stderr}: & \% & the standard error stream\\
\asexp{stdout}: & \% & the standard output stream\\
\asexp{textWriter}: & (\astype{Character} $\to$ ()) $\to$ \% & create a stream\\
\asexp{textWriter}:
& (\astype{Character} $\to$ (), () $\to$ ()) $\to$ \% & create a stream\\
\asexp{write!}: & (\astype{Character}, \%) $\to$ () & write to a stream\\
\end{exports}
#endif

TextWriter: with {
	flush!: % -> %;
#if ALDOC
\aspage{flush!}
\Usage{\name~s}
\Signature{\%}{\%}
\Params{ {\em s} & \% & a stream\\ }
\Descr{\name(s) causes all previous values inserted into s to be really
written and returns the stream.
Has no effect on unbuffered streams, such as \asexp{stderr}.}
#endif
	stderr: %;
	stdout: %;
#if ALDOC
\aspage{stderr,stdout}
\astarget{stderr}
\astarget{stdout}
\Usage{stderr\\stdout}
\Signature{}{\%}
\Retval{stderr and stdout are the standard error and standard
output streams respectively.}
#endif
	textWriter: (Ch -> ()) -> %;
	textWriter: (Ch -> (), () -> ()) -> %;
#if ALDOC
\aspage{textWriter}
\Usage{\name~f\\ \name(f, g)}
\Signatures{
\name: & (\astype{Character} $\to$ ()) $\to$ \%\\
\name: & (\astype{Character} $\to$ (), () $\to$ ()) $\to$ \%\\
}
\Params{
{\em f} & \astype{Character} $\to$ () & the single--character write function\\
{\em g} & () $\to$ () & the flush function (optional)\\
}
\Retval{Returns the output stream for which $f(c)$ writes the character $c$
and such that $g()$ flushes the stream.
If g is not given, then flushing the resulting stream has no effect.}
#endif
	write!: (Ch, %) -> ();
#if ALDOC
\aspage{write!}
\Usage{\name(c, s)}
\Signature{(\astype{Character}, \%)}{()}
\Params{
{\em c} & \astype{Character} & character to write\\
{\em s} & \% & a stream\\
}
\Retval{Writes the character $c$ to the stream $s$ and returns $c$.}
#endif
} == add {
	Rep == Record(write: Ch -> (), flush: () -> ());

	import {
		fflush: Pointer -> Z;
		-- TEMPO: NEEDS A TYPE FOR C-int
		fputc: (Z, Pointer) -> Z;
		-- fputc: (CInteger, Pointer) -> CInteger;
		stderrFile: () -> Pointer;
		stdoutFile: () -> Pointer;
	} from Foreign C;

	local cwriter(s:Pointer):% == {
		import from Rep;
		per [putc! s, flush s];
	}

	local putc!(s:Pointer)(c:Ch):()	== fputc(ord c, s);
	local flush(s:Pointer)():()	== fflush s;
	write!(c:Ch, s:%):()		== { import from Rep; rep(s).write(c); }
	local nop():()			== {};
	textWriter(f:Ch -> ()):%	== textWriter(f, nop);
	stderr:%			== cwriter stderrFile();
	stdout:%			== cwriter stdoutFile();

	flush!(s:%):% == {
		import from Rep;
		rep(s).flush();
		s;
	}

	textWriter(f:Ch -> (), g:() -> ()):% == {
		import from Rep;
		per [f, g];
	}
}

