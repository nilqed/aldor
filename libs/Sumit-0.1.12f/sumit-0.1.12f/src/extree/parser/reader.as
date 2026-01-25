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
------------------------------- reader.as ----------------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1995

#include "sumit"

macro {
	CHAR		== Character;
	PCHAR		== Partial Character;
	TEXT		== TextReader;
}

#if ALDOC
\thistype{SumitReader}
\History{Manuel Bronstein}{23/11/95}{created}
\Usage{import from \this}
\Descr{\this~is an extension of TextReader with character pushback.
In addition, it allows a string to be converted into a reader.}
\begin{exports}
end?: & \this $\to$ Boolean & Check for end of input\\
push!: & (Character, \this) $\to$ \this & Push back a character\\
read!: & \this $\to$ Character & Read a character\\
% reader: & String $\to$ \this & Create a reader\\
reader: & TextReader $\to$ \this & Create a reader\\
\end{exports}
#endif

SumitReader: with {
	end?: % -> Boolean;
#if ALDOC
\aspage{end?}
\Usage{\name~p}
\Signature{\this}{Boolean}
\Params{ {\em p} & \this & A text reader\\ }
\Retval{Returns \true~if $p$ is at the end of its input, \false~otherwise.}
#endif
	push!: (CHAR, %) -> %;
#if ALDOC
\aspage{push!}
\Usage{\name(c, p)}
\Signature{(Character, \this)}{\this}
\Params{
{\em c} & Character & A character \\
{\em p} & \this & A text reader\\
}
\Descr{\name(c, p) pushes $c$ back onto $p$, so $c$ will be the next character
read. More than one character can be pushed back on a reader.}
#endif
	read!: % -> CHAR;
#if ALDOC
\aspage{read!}
\Usage{\name~p}
\Signature{\this}{Character}
\Params{ {\em p} & \this & A text reader\\ }
\Retval{Returns the next character read from the reader $p$.}
#endif
	reader: TEXT -> %;
#if ALDOC
\aspage{reader}
\Usage{\name~p}
\Signature{TextReader}{\this}
\Params{ {\em p} & TextReader & A text reader\\ }
\Retval{Converts $p$ to a \this~and returns the result.}
#endif
	-- reader: String -> %;
} == add {
	macro Rep == Record(pushback:List CHAR, rdr:TEXT);

	import from Rep;

	eof:CHAR		== { import from SingleInteger; char 0; }
	reader(t:TEXT):%	== per [empty(), t];
	cache(t:%):List(CHAR)	== rep(t).pushback;
	txtreader(t:%):TEXT	== rep(t).rdr;
	empty?(t:%):Boolean	== empty? cache t;
	end?(t:%):Boolean	== empty? t and check? t;

	check?(t:%):Boolean == {
		ASSERT empty? t;
		c := readchar!(txtreader t, eof);
		c = eof => true;
		push!(c, t);
		false;
	}

	push!(c:CHAR, t:%):% == {
		rep(t).pushback := cons(c, cache t);
		t;
	}

	pop!(t:%):CHAR == {
		c := first(l := cache t);
		rep(t).pushback := rest l;
		c;
	}

	read!(t:%):CHAR == {
		empty? t => readchar! txtreader t;
		pop! t;
	}
}
