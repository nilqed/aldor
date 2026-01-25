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
------------------------------- stdutil.as ----------------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1994

#include "sumit"

#if ASDOC
\thistype{StandardUtilities}
\History{Manuel Bronstein}{17/6/94}{created}
\Usage{import from \this}
\Descr{\this~provides utilities normally found in standard libraries.}
\begin{exports}
decimal: & Z $\to$ String & converts an integer to decimal\\
decimal: & String $\to$ Z & converts a string to an integer\\
decimal?: & String $\to$ Boolean &
tests if a string contains a decimal integer\\
flag: & C $\to$ List String & gets the value of a command line flag\\
flag? & C $\to$ Boolean & tests whether a command line flag is present\\
getint: & (InFile, C) $\to$ C & reads an integer from a stream\\
getstring: & (InFile, Z, C) $\to$ String & reads n characters from a stream\\
seek: & (InFile, Z, Z) $\to$ Boolean & sets the position of an input port\\
tell: & InFile $\to$ Z & returns the current position of a port\\
uniqueName: & String $\to$ String & returns a unique filename\\
wordSize: & -> Z & returns the number of bits in a word\\
\end{exports}
\Aswhere{
Z &==& SingleInteger\\
C &==& Character\\
}
#endif

macro {
	Z 	== SingleInteger;
	FLGSIGN == char "-";
}

import from Character, Z;

StandardUtilities: with {
	decimal: Z -> String;
	decimal: String -> Z;
	decimal?: String -> Boolean;
#if ASDOC
\begin{aspage}{decimal}
\Usage{ \name~n\\ \name?~s }
\Signatures{
\name: & SingleInteger $\to$ String\\
\name: & String $\to$ SingleInteger\\
\name?: & String $\to$ Boolean\\
}
\Params{
{\em n} & SingleInteger & The integer to convert to a string\\
{\em s} & String & The string to test or convert to an integer\\
}
\Retval{
\name(n) returns a string containing the decimal representation of n.\\
\name(s) returns the decimal value of s if it is a SingleInteger\\
\name?(s) returns \true~if s contains a decimal SingleInteger,
\false~otherwise.
}
\begin{asex}
The following code assigns the string ``-130'' to s, checks that it is a
valid decimal string and converts it back to an integer n, which has then
the value -130.
\begin{ttyout}
import from SingleInteger, StandardUtilities;
s := decimal(-130);
if decimal? s then n := decimal s;
\end{ttyout}
\end{asex}
\end{aspage}
#endif
	flag: (Character, s:String == "") -> List String;
	flag?: (Character, s:String == "") -> Boolean;
#if ASDOC
\begin{aspage}{flag}
\Usage{ \name~c\\ \name(c, s)\\ \name?~c\\ \name?(c, s) }
\Signatures{
\name: & (Character, .:String == "") $\to$ List String\\
\name?: & (Character, .:String == "") $\to$ Boolean\\
}
\Params{
{\em c} & Character & Flag code to look for\\
{\em s} & String &
Flag codes that cause the rest of the argument to be ignored\\
}
\Retval{
\name(c, s) returns all the values of the flag c each time it is present
in the command line, an empty list otherwise.\\
\name?(c, s) returns \true~if the flag c is present in the command line,
\false~otherwise.\\
In both functions, s contains an optional list of flag codes which cause
the rest of the argument to be skipped.
}
\end{aspage}
#endif
	getint: (InFile, eof:Character == char 0) -> Z;
#if ASDOC
\begin{aspage}{getint}
\Usage{ \name~p\\ \name(p, eof) }
\Signature{(InFile, .:Character == char 0)}{Z}
\Params{
{\em p} & InFile & An input port corresponding to a file\\
{\em eof} & Character & The eof character (default = char 0)\\
}
\Descr{\name(p, eof) reads an integer (binary-coded) from the input port p.}
\Retval{Returns the integer read, or 0 if eof is encountered.}
\end{aspage}
#endif
	getstring: (InFile, Z, eof:Character == char 0) -> String;
#if ASDOC
\begin{aspage}{getstring}
\Usage{ \name(p, n)\\ \name(p, n, eof) }
\Signature{(InFile, SingleInteger, .:Character == char 0)}{String}
\Params{
{\em p} & InFile & A input port corresponding to a file\\
{\em n} & SingleInteger & The number of characters to read\\
{\em eof} & Character & The eof character (default = char 0)\\
}
\Descr{\name(p, n, eof) reads n characters from the input port p, or until
the eof character is encountered.}
\Retval{Returns a string containing all the characters read.}
\end{aspage}
#endif
	seek: (InFile, Z, op:Z == 0) -> Boolean;
#if ASDOC
\begin{aspage}{seek}
\Usage{ \name(p, n)\\ \name(p, n, op) }
\Signature{(InFile, SingleInteger, .:SingleInteger == 0)}{Boolean}
\Params{
{\em p} & InFile & A input port corresponding to a file\\
{\em n} & SingleInteger & The offset to position the port to\\
{\em op} & SingleInteger & The operation code (default = 0)\\
}
\Descr{\name(p, n, op) sets the position of the input port p to n bytes from
either the beginning of the input port (if op = 0), the current position
(if op = 1), or the end of the input port (if op = 2).}
\Retval{Returns \true~if the seek cannot be done, \false~if it has been done
successfully.}
\seealso{tell(\this)}
\end{aspage}
#endif
	tell: InFile -> Z;
#if ASDOC
\begin{aspage}{tell}
\Usage{\name~p}
\Signature{InFile}{SingleInteger}
\Params{ {\em p} & InFile & A input port corresponding to a file\\ }
\Retval{Returns the current position relative to the beginning
of the input port p.}
\seealso{seek(\this)}
\end{aspage}
#endif
	uniqueName: String -> String;
#if ASDOC
\aspage{uniqueName}
\Usage{\name~s}
\Signature{String}{String}
\Params{ {\em s} & String & A root string\\ }
\Retval{Returns a unique name in the file system starting with s.}
#endif
	wordSize: Z;
#if ASDOC
\aspage{wordSize}
\Usage{\name}
\Signature{}{SingleInteger}
\Retval{Returns the number of bits in a word.}
#endif
} == add {
	import from Character, Z;
	import {
		atol: String -> Z;
		fseek: (InFile, Z, Z) -> Z;
		ftell: InFile -> Z;
		ltoa: (Z, String) -> String;
		mktemp: String -> String;
		readint: InFile -> Z;
	} from Foreign C;

	decimal(n:Z):String				== ltoa(n, new 10);
	tell(p:InFile):Z				== ftell p;
	seek(p:InFile, n:Z, op:Z == 0):Boolean		== fseek(p, n, op) < 0;
	getint(p:InFile, eof:Character == char 0):Z	== readint p;
	uniqueName(s:String):String		== mktemp concat(s, "XXXXXX");

	wordSize:Z == {
		maxint:Z := max;
		ASSERT(maxint >= 2147483647);
		maxint = 2147483647 => 32;
		64;
	}

	decimal(s:String):Z == {
		ASSERT decimal? s;
		atol s;
	}

	getstring(p:InFile, n:Z, eof:Character == char 0):String == {
		s := new n;
		for i in 1..n repeat s.i := readchar!(p, eof);
		s;
	}

	flag?(c:Character, s:String == ""):Boolean == {
		import from List String;
		not empty? flag(c, s);
	}

	flag(c:Character, s:String == ""):List String == {
		ASSERT(c ~= FLGSIGN);
		import from Array String, CommandLine, Partial String;
		n := #arguments;
		l:List String := empty();
		for i in 1..n | arguments.i.1 = FLGSIGN repeat {
			t := { i = n => ""; arguments(i+1) };
			if not failed?(u := flag(arguments.i, t, s, c)) then
				l := cons(retract u, l);
		}
		l;
	}

	local flag(arg:String,t:String,s:String,c:Character):Partial String == {
		ASSERT(arg.1 = FLGSIGN);
		n := #arg;
		for i in 2..n-1 repeat {
			arg.i = c => return [arg(i+1..)];
			member?(arg.i, s) => return failed;
		}
		arg.n = c => [t];
		failed;
	}

	local member?(c:Character, s:String):Boolean == {
		for ch in s repeat c = ch => return true;
		false;
	}

	decimal?(s:String):Boolean == {
		zero? #s => false;
		(c := s.1) = char " " => decimal? s(2..);
		(c = char "-" or c = char "+" or digit? c) and decimal0? s(2..);
	}

	local decimal0?(s:String):Boolean == {
		for c in s repeat not digit? c => return false;
		true;
	}
}

#if SUMITTEST
---------------------- test stdutil.as --------------------------
#include "sumittest"

import from SingleInteger, StandardUtilities;

decimal():Boolean == {
	import from Integer, RandomNumberGenerator;
	n:SingleInteger := retract randomInteger();
	s := decimal n;
	m := decimal s;
	n = m;
}

seek():Boolean == {
	import from InFile, FileName;
	open?(f := open filename "Tstdutil") => {
		seek(f, 10) => false;
		n := getint f;
		m := tell f;
		close f;
		w := wordSize;
		w = 64 => m = 18;
		m = 14;
	}
	false;
}

-- command line must have "-v -b -Lfoo -abar"
flags():Boolean == {
	import from String, List String;
	prefix := "aleoBCDFILMPQRSUW";
	boolean := "bcdfghijkmnpqrstuvwxyzAEGHJKNOTWXYZ";
	boolfound := "";
	preffound := "";
	for i in 1..#boolean | flag?(boolean.i, prefix) repeat
		boolfound := concat(boolfound, boolean(i..i));
	for i in 1..#prefix repeat {
		l := flag(prefix.i, prefix);
		if not empty? l then {
			preffound := concat(preffound, prefix(i..i));
			for s in l repeat preffound := concat(preffound, s);
		}
	}
	boolfound = "bv" and preffound = "abarLfoo";
}

print << "Testing stdutil..." << newline;
sumitTest("decimal", decimal);
sumitTest("seek", seek);
sumitTest("flags", flags);
print << "    Wordsize = " << wordSize << newline;
print << newline;
#endif
