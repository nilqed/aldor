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
---------------------------- sal_cmdline.as ----------------------------------
--
-- This file provides utilities for command-line processing
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro {
	PA == PrimitiveArray;
	A  == Array;
	Ch == Character;
	Z  == MachineInteger;
}

#if ALDOC
\thistype{CommandLine}
\History{Manuel Bronstein}{7/10/98}{created}
\Usage{import from \this}
\Descr{\this~provides utilities for command-line processing.}
\begin{exports}
\asexp{arguments}: & \astype{Array} \astype{String} & command line arguments\\
\asexp{command}: & \astype{String} & command line command\\
\asexp{flag}: & \astype{Character} $\to$ \astype{List} \astype{String}
& value of a command line flag\\
\asexp{flag?}: & \astype{Character} $\to$ \astype{Boolean} &
test for a command line flag\\
\end{exports}
#endif

CommandLine: with {
	arguments: A String;
#if ALDOC
\aspage{arguments}
\Usage{\name}
\Signature{}{\astype{Array} \astype{String}}
\Retval{Returns an array containing all the arguments of the command line,
the command itself is not included.}
#endif
	command: String;
#if ALDOC
\aspage{command}
\Signature{}{\astype{String}}
\Retval{Returns the command, \ie the first word of the command line.}
#endif
	flag: (Ch, s:String == empty) -> List String;
	flag?: (Ch, s:String == empty) -> Boolean;
#if ALDOC
\aspage{flag}
\astarget{\name?}
\Usage{ \name~c\\ \name(c, s)\\ \name?~c\\ \name?(c, s) }
\Signatures{
\name:& \astype{Character} $\to$ \astype{List} \astype{String}\\
\name:& (\astype{Character},\astype{String})$\to$\astype{List} \astype{String}\\
\name?: & \astype{Character} $\to$ \astype{Boolean}\\
\name?: & (\astype{Character}, \astype{String}) $\to$ \astype{Boolean}\\
}
\Params{
{\em c} & \astype{Character} & flag code to look for\\
{\em s} & \astype{String} & special flag codes (optional)\\
}
\Retval{
\name(c) returns all the values of the flag c each time it is present
in the command line, an empty list otherwise.\\
\name?(c) returns \true~if the flag c is present in the command line,
\false~otherwise.\\
In both functions, the optional argument s contains a list of
flag codes which cause the rest of the argument to be skipped.
}
\begin{asex}
If the command line to the program was {\tt myprog -lsalli -l gmp -v}, then
{\tt \name?(char "a")} and {\tt \name?(char "v")} both return \true, while
{\tt \name?(char "b")} and {\tt \name?(char "a", "l")} both return \false.
In addition, {\tt \name(char "l")} returns the list {\tt [``salli'', ``gmp'']}.
\end{asex}
#endif
} == add {
	import {
		mainArgc:  Z;
		mainArgv:  Pointer;
	} from Foreign C;

	import from Z, A String;

	-- The following is for safe conversion in the debug version
	local argv:PA Pointer	== array(mainArgv, mainArgc);

	command:String		== { import from PA Pointer; string argv 0; }
	local flagsign:Ch	== { import from String; char "-"; }

	arguments:A String == {
		import from PA Pointer;
		local locala:A String := new(prev mainArgc, "");
		for locali in 0..prev prev mainArgc repeat
			locala.locali := string argv(next locali);
		locala;
	}

	flag?(c:Ch, s:String):Boolean == {
		import from List String;
		not empty? flag(c, s);
	}

	local nextarg(i:Z, n:Z):String == {
		(i := next i) = n => empty;
		arguments i;
	}

	flag(c:Ch, s:String):List String == {
		assert(c ~= flagsign);
		import from A String, Partial String, Z;
		n := #arguments;
		l:List String := empty;
		for i in 0..prev n repeat {
			if char(arguments.i) = flagsign then {
				u := flag(arguments.i, nextarg(i, n), s, c);
				if not failed? u then l := cons(retract u, l);
			}
		}
		reverse l;
	}

	local flag(arg:String, t:String, s:String, c:Ch):Partial String == {
		import from Z;
		assert(char arg = flagsign);
		n := prev(#arg);
		for i in 1..prev n repeat {
			arg.i = c => return [arg + next i];
			member?(arg.i, s) => return failed;
		}
		arg.n = c => [t];
		failed;
	}
}

#if SALLITEST
---------------------- test sal_command.as --------------------------
#include "sallitest"

-- command line must have "-v -b -Lfoo -abar"
local flags():Boolean == {
	import from String, List String, CommandLine;
	prefix := "aleoBCDFILMPQRSUW";
	boolean := "bcdfghijkmnpqrstuvwxyzAEGHJKNOTWXYZ";
	boolfound := "";
	for c in boolean | flag?(c, prefix) repeat
		boolfound := boolfound + c::String;
	preffound := "";
	for c in prefix repeat {
		l := flag(c, prefix);
		if ~empty?(l) then {
			preffound := preffound + c::String;
			for s in l repeat preffound := preffound + s;
		}
	}
	boolfound = "bv" and preffound = "abarLfoo";
}

stderr << "Testing sal__command..." << newline;
salliTest("flags", flags);
stderr << newline;
#endif

