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
------------------------------- sit_symbol.as ----------------------------------
--
-- Symbols, i.e. read-only strings with O(1) comparison
--
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "salli"

#if ALDOC
\thistype{Symbol}
\History{Manuel Bronstein}{30/6/99}{created}
\Usage{import from \this}
\Descr{\this provides symbols,~\ie read--only strings with
constant--time comparison.}
\begin{exports}
\category{\astype{HashType}}\\
\category{\astype{InputType}}\\
\category{\astype{SerializableType}}\\
\category{\astype{SumitType}}\\     % DOCUMENT HERE, BUT EXTEND LATER
\asexp{$-$}: & \astype{String} $\to$ \% & Create a symbol\\
\asexp{name}: & \% $\to$ \astype{String} & Name of a symbol\\
\asexp{new}: & () $\to$ \% & Create a new symbol\\
Subscripted name of a symbol\\
\end{exports}
#endif

macro {
	Z	== MachineInteger;
	PZ	== Record(cnt:Z);
	H	== HashTable(String, String);
	SIZE	== 16384;
}

Symbol: Join(HashType, InputType, OutputType, SerializableType) with {
	-:  String -> %;
#if ALDOC
\aspage{$-$}
\Usage{$-s$}
\Signature{\astype{String}}{\%}
\Params{{\em s} & \astype{String} & A string\\ }
\Retval{Returns s as a symbol.}
#endif
	name: % -> String;
#if ALDOC
\aspage{name}
\Usage{\name~s}
\Signature{\%}{\astype{String}}
\Params{{\em s} & \% & A symbol\\ }
\Retval{Returns a new copy of the name of s.}
\Remarks{Modifying \name(s) does not modify s, since a new copy
is created at each call.}
#endif
	new: () -> %;
#if ALDOC
\aspage{new}
\Usage{\name()}
\Signature{()}{\%}
\Retval{Returns a new symbol.}
#endif
} == add {
	Rep == String;

	local stable:H		== { import from Z, String; table SIZE }
	local enter(s:String):%	== { stable.s := s; per s }
	local root:String	== "%SumitSymbol";
	-- local buffer:String	== "012345678901234567890"; -- enough for 2^64
	local buffer:String	== { import from Z; new 21 } -- enough for 2^64
	local counter:PZ	== { import from Z; [0] }
	name(s:%):String	== { import from String; copy rep s }
	(s:%) = (t:%):Boolean	== { import from Pointer; address s = address t}
	<< (p:TextReader):%	== { import from String; -(<< p); }
	<< (p:BinaryReader):%	== { import from String; -(<< p); }
	(p:TextWriter) << (s:%):TextWriter	== { import from Rep;p << rep s}
	(p:BinaryWriter) << (s:%):BinaryWriter	== { import from Rep;p << rep s}
	local address(s:%):Pointer		== s pretend Pointer;

	-- use address-based hashing in order to speed-up symbol-table lookup
	hash(s:%):Z		== { import from Pointer; address(s)::Z }

	new():% == {
		import from TextWriter, String, Partial String;
		import from H, Z, PZ, Character;
		for c in next(counter.cnt).. repeat {
			buffer::TextWriter << c << null;
			s := root + buffer;
			failed? find(stable, s) => {
				counter.cnt := c;
				return enter s;
			}
		}
		never;
	}

	-(s:String):% == {
		import from H, Partial String;
		failed?(u := find(stable, s)) => enter copy s;
		per retract u;
	}

}
