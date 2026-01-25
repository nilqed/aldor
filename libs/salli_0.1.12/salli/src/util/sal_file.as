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
------------------------------- sal_file.as ----------------------------------
--
-- This file provides an interface to the C FILE* type
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

#if ALDOC
\thistype{File}
\History{Manuel Bronstein}{14/10/98}{created}
\History{Manuel Bronstein}{21/10/99}{added exceptions}
\Usage{import from \this}
\Descr{\this~is a type whose elements are operating system files.}
\begin{exports}
\asexp{close!}: & \% $\to$ () & close a file\\
\asexp{coerce}:
& \% $\to$ \astype{BinaryReader} & conversion to a binary input stream\\
\asexp{coerce}:
& \% $\to$ \astype{BinaryWriter} & conversion to a binary output stream\\
\asexp{coerce}:
& \% $\to$ \astype{TextReader} & conversion to a text input stream\\
\asexp{coerce}:
& \% $\to$ \astype{TextWriter} & conversion to a text output stream\\
\asexp{fileAppend}: & \astype{MachineInteger} & mode for \asexp{open}\\
\asexp{fileBinary}: & \astype{MachineInteger} & mode for \asexp{open}\\
\asexp{fileRead}: & \astype{MachineInteger} & mode for \asexp{open}\\
\asexp{fileText}: & \astype{MachineInteger} & mode for \asexp{open}\\
\asexp{fileWrite}: & \astype{MachineInteger} & mode for \asexp{open}\\
\asexp{open}:
& (\astype{String}, \astype{MachineInteger}) $\to$ \% & open a file\\
\asexp{remove}: & \astype{String} $\to$ () & removes a file\\
\asexp{uniqueName}:
& \astype{String} $\to$ \astype{String} & get a unique filename\\
\end{exports}
#endif

macro {
	Ch == Character;
	Z  == MachineInteger;
}

File: with {
	close!: % -> ();
#if ALDOC
\aspage{close!}
\Usage{\name~f}
\Signature{\%}{()}
\Params{ {\em f} & \% & a file\\ }
\Descr{Closes the file f.}
#endif
	coerce: % -> TextReader;
	coerce: % -> TextWriter;
	coerce: % -> BinaryReader;
	coerce: % -> BinaryWriter;
#if ALDOC
\aspage{coerce}
\Usage{f::BinaryReader\\ f::BinaryWriter\\ f::TextReader\\ f::TextWriter}
\Signatures{
\name: & \% $\to$ \astype{BinaryReader}\\
\name: & \% $\to$ \astype{BinaryWriter}\\
\name: & \% $\to$ \astype{TextReader}\\
\name: & \% $\to$ \astype{TextWriter}\\
}
\Params{ {\em f} & \% & a file\\ }
\Descr{Converts the file f to to a binary or text reader or writer.
This is necessary before reading from or writing to the file. The file must
have been opened in an appropriate mode for reading or writing respectively.}
\Remarks{Coercing a file to a reader or writer allocates memory, so it
is advisable to assign the resulting stream to a variable. Unlike the ones
for \astype{String}, those coercions do not reset the file to its beginning.}
#endif
	fileAppend: Z;
	fileBinary: Z;
	fileRead: Z;
	fileText: Z;
	fileWrite: Z;
#if ALDOC
\aspage{fileAppend,fileBinary,fileRead,fileText,fileWrite}
\astarget{fileAppend}
\astarget{fileBinary}
\astarget{fileRead}
\astarget{fileText}
\astarget{fileWrite}
\Usage{fileAppend\\ fileBinary\\ fileRead\\ fileText\\ fileWrite}
\Signature{}{\astype{MachineInteger}}
\Descr{Those constants are for use in the mode parameter of the
\asexp{open} function.}
#endif
	open: (String, n:Z == fileRead) -> %;
#if ALDOC
\aspage{open}
\Usage{\name(s,m)}
\Signature{(\astype{String}, \astype{MachineInteger})}{\%}
\Params{
{\em s} & \astype{String} & a filename\\
{\em m} & \astype{MachineInteger} & a mode (optional)\\
}
\Descr{Opens the file with the name s in the mode m,
and returns the opened file. The mode is any combination of the constants
\asexp{fileAppend}, \asexp{fileRead},
and \asexp{fileWrite}, together with one of \asexp{fileBinary}
or \asexp{fileText}, grouped together
with \asfunc{MachineInteger}{+} or \asfunc{MachineInteger}{$\backslash/$}.
The default is \asexp{fileRead} + \asexp{fileText}.}
\Remarks{\name~returns \asfunc{Pointer}{nil} and throws the
exception \astype{FileException} if the file cannot be opened for
any reason.}
#endif
	remove: String -> ();
#if ALDOC
\aspage{remove}
\Usage{\name~s}
\Signature{\astype{String}}{()}
\Params{ {\em s} & \astype{String} & A file name\\ }
\Descr{Removes the file with name s in the file system.}
#endif
	uniqueName: String -> String;
#if ALDOC
\aspage{uniqueName}
\Usage{\name~s}
\Signature{\astype{String}}{\astype{String}}
\Params{ {\em s} & \astype{String} & A root string\\ }
\Retval{Returns a unique name with prefix s in the file system.}
#endif
} == add {
	Rep == Pointer;

	import {
		fclose: Pointer -> Z;
		fflush: Pointer -> Z;
		fgetc: Pointer -> Z;
		-- TEMPO: NEEDS A TYPE FOR C-int
		-- fputc: (CInteger, Pointer) -> CInteger;
		-- ungetc: (CInteger, Pointer) -> CInteger;
		fputc: (Z, Pointer) -> Z;
		lungetc: (Z, Pointer) -> Z;
	} from Foreign C;

	-- bit mask for open-mode:
	--	b0    =  0 = noread,   1 = read
	--	b1    =  0 = nowrite,  1 = write
	--	b2    =  0 = noappend, 1 = append
	--	b3    =  0 = text,     1 = binary
	fileAppend:Z		== 4;
	fileBinary:Z		== 8;
	fileRead:Z		== 1;
	fileText:Z		== 0;
	fileWrite:Z		== 2;
	close!(file:%):()	== fclose rep file;
	local putb!(s:Pointer)(b:Byte):()	== fputc(b::Z, s);
	local putc!(s:Pointer)(c:Ch):()		== fputc(ord c, s);
	local getb(s:Pointer)():Byte		== lowByte fgetc s;
	local getc(s:Pointer)():Ch		== char fgetc s;
	local push(s:Pointer)(c:Ch):()		== lungetc(ord c, s);
	local flush(s:Pointer)():()		== fflush s;
	local ok?(file:%):Boolean	== { import from Rep; ~nil?(rep file) }

	uniqueName(s:String):String == {
		import { mktemp: Pointer -> Pointer } from Foreign C;
		string mktemp pointer(s + "XXXXXX");
	}

	remove(s:String):() == {
		import { unlink: Pointer -> Z } from Foreign C;
		unlink pointer s;
	}

	coerce(file:%):BinaryWriter == {
		assert(ok? file);
		binaryWriter(putb! rep file, flush rep file);
	}

	coerce(file:%):BinaryReader == {
		assert(ok? file);
		binaryReader getb rep file;
	}

	coerce(file:%):TextWriter == {
		assert(ok? file);
		textWriter(putc! rep file, flush rep file);
	}

	coerce(file:%):TextReader == {
		assert(ok? file);
		textReader(getc rep file, push rep file);
	}

	open(name:String, mode:Z):% == {
		import from Rep;
		import { fopen:(Pointer,Pointer) -> Pointer; } from Foreign C;
		read? := bit?(mode, 0);
		write? := bit?(mode, 1);
		s:String := {
			bit?(mode, 2) => "a";
			read? => "r";
			write? => "w";
			empty;
		}
		if read? and write? then s := s + "+";
		if bit?(mode, 3) then s := s + "b";
		empty? s or nil?(ptr := fopen(pointer name, pointer s)) =>
							throw FileException;
		per ptr;
	}
}

#if ALDOC
\thistype{FileException}
\History{Manuel Bronstein}{21/10/99}{created}
\Usage{
throw \this\\
try \dots catch E in \{ E has \astype{FileExceptionType} => \dots \}
}
\Descr{\this~is an exception type thrown by file operations.}
#endif
FileException: FileExceptionType == add;

#if ALDOC
\thistype{FileExceptionType}
\History{Manuel Bronstein}{21/10/99}{created}
\Usage{\this: Category}
\Descr{\this~is the category of exceptions thrown by file operations.}
#endif
define FileExceptionType:Category == with;
