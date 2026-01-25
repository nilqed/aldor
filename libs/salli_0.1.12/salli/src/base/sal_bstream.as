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
---------------------------- sal_bstream.as ---------------------------------
--
-- This file defines binary read/write streams
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro Z == MachineInteger;

#if ALDOC
\thistype{BinaryReader}
\History{Manuel Bronstein}{1/10/98}{created}
\Usage{import from \this}
\Descr{\this~provides various binary input streams.}
\begin{exports}
\asexp{bin}: & \% & standard input stream\\
\asexp{binaryReader}: & () $\to$ \astype{Byte} $\to$ \% & create a stream\\
\asexp{read!}: & \% $\to$ \astype{Byte} & read from a stream\\
\end{exports}
#endif

BinaryReader: with {
	bin: %;
#if ALDOC
\aspage{bin}
\Usage{\name}
\Signature{}{\%}
\Retval{bin is the standard input stream.}
#endif
	binaryReader: (() -> Byte) -> %;
#if ALDOC
\aspage{binaryReader}
\Usage{\name~f}
\Signature{(() $\to$ \astype{Byte})}{\%}
\Params{ {\em f} & () $\to$ \astype{Byte} & the single--byte read function\\ }
\Retval{Returns the input stream for which $f()$ reads a byte.}
#endif
	read!: % -> Byte;
#if ALDOC
\aspage{read!}
\Usage{\name~s}
\Signature{\%}{\astype{Byte}}
\Params{ {\em s} & \% & a stream\\ }
\Retval{Reads a byte from $s$ and returns it. Some streams may return
the byte \asfunc{Byte}{eof} if the end of file is reached.}
#endif
} == add {
	macro Rep == (() -> Byte);

	import {
		fgetc: Pointer -> Z;
		stdinFile: () -> Pointer;
	} from Foreign C;

	binaryReader(f:() -> Byte):%	== per f;
	local getc(s:Pointer)():Byte	== lowByte fgetc s;
	read!(s:%):Byte			== rep(s)();
	local creader(s:Pointer):%	== per getc s;
	bin:%				== creader stdinFile();
}

#if ALDOC
\thistype{BinaryWriter}
\History{Manuel Bronstein}{8/12/98}{created}
\Usage{import from \this}
\Descr{\this~provides various binary output streams.}
\begin{exports}
\asexp{berr}: & \% & the binary standard error stream\\
\asexp{bout}: & \% & the binary standard output stream\\
\asexp{binaryWriter}:
& (\astype{Byte} $\to$ ()) $\to$ \% & create a stream\\
\asexp{binaryWriter}:
& (\astype{Byte} $\to$ (), () $\to$ ()) $\to$ \% & create a stream\\
\asexp{flush!}: & \% $\to$ \% & flush a stream\\
\asexp{write!}: & (\astype{Byte}, \%) $\to$ () & write to a stream\\
\end{exports}
#endif

BinaryWriter: with {
	berr: %;
	bout: %;
#if ALDOC
\aspage{berr,bout}
\astarget{berr}
\astarget{bout}
\Usage{berr\\bout}
\Signature{}{\%}
\Retval{berr and bout are the binary standard error and standard
output streams respectively.}
#endif
	binaryWriter: (Byte -> ()) -> %;
	binaryWriter: (Byte -> (), () -> ()) -> %;
#if ALDOC
\aspage{binaryWriter}
\Usage{\name~f\\ \name(f, g)}
\Signatures{
\name: & (\astype{Byte} $\to$ ()) $\to$ \%\\
\name: & (\astype{Byte} $\to$ (), () $\to$ ()) $\to$ \%\\
}
\Params{
{\em f} & \astype{Byte} $\to$ () & the single--byte write function\\
{\em g} & () $\to$ () & the flush function (optional)\\
}
\Retval{Returns the output stream for which $f(c)$ writes the byte $c$
and such that $g()$ flushes the stream.
If g is not given, then flushing the resulting stream has no effect.}
#endif
	flush!: % -> %;
#if ALDOC
\aspage{flush!}
\Usage{\name~s}
\Signature{\%}{\%}
\Params{ {\em s} & \% & a stream\\ }
\Descr{\name(s) causes all previous values inserted into s to be really
written and returns the stream.
Has no effect on unbuffered streams, such as \asexp{berr}.}
#endif
	write!: (Byte, %) -> ();
#if ALDOC
\aspage{write!}
\Usage{\name(c, s)}
\Signature{(\astype{Byte}, \%)}{()}
\Params{
{\em c} & \astype{Byte} & byte to write\\
{\em s} & \% & a stream\\
}
\Retval{Writes the byte $c$ to the stream $s$ and returns $c$.}
#endif
} == add {
	Rep == Record(write: Byte -> (), flush: () -> ());

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
		per [put! s, flush s];
	}

	local put!(s:Pointer)(c:Byte):()== fputc(c::Z, s);
	local flush(s:Pointer)():()	== fflush s;
	write!(c:Byte, s:%):()		== { import from Rep; rep(s).write(c); }
	local nop():()			== {};
	binaryWriter(f:Byte -> ()):%	== binaryWriter(f, nop);
	berr:%				== cwriter stderrFile();
	bout:%				== cwriter stdoutFile();

	flush!(s:%):% == {
		import from Rep;
		rep(s).flush();
		s;
	}

	binaryWriter(f:Byte -> (), g:() -> ()):% == {
		import from Rep;
		per [f, g];
	}
}
