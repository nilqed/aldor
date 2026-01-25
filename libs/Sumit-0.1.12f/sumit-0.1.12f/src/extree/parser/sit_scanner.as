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
------------------------------- sit_scanner.as --------------------------------
--
-- Lexical scanner
--
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"
#include "tokens"

macro {
	CHAR		== Character;
	PCHAR		== Partial Character;
	TEXT		== TextReader;
}

#if ALDOC
\thistype{Scanner}
\History{Manuel Bronstein}{23/11/95}{created}
\History{Manuel Bronstein}{20/09/96}{added /* */ and conversion ** --> ^}
\History{Manuel Bronstein}{12/05/97}{added scanning of floats}
\History{Manuel Bronstein}{15/12/97}{added scanning of < > <= >=}
\Usage{import from \this}
\Descr{\this~provides a simple scanner for mathematical expressions.}
\begin{exports}
\asexp{scan}: & \astype{TextReader} $\to$ \astype{Token} & Scan a token\\
\end{exports}
#endif

Scanner: with {
	scan!: TEXT -> Token;
#if ALDOC
\aspage{scan}
\Usage{\name~p}
\Signature{\astype{TextReader}}{\astype{Token}}
\Params{ {\em p} & \astype{TextReader} & Text to scan\\ }
\Retval{Returns the next token read from the reader $p$.}
#endif
} == add {
	import from String;

	local colon:CHAR	== char ":";
	local equal:CHAR	== char "=";
	local star:CHAR		== char "*";
	local slash:CHAR	== char "/";
	local bslash:CHAR	== char "\";
	local comma:CHAR	== char ",";
	local lpar:CHAR		== char "(";
	local rpar:CHAR		== char ")";
	local lcurly:CHAR	== char "{";
	local rcurly:CHAR	== char "}";
	local langle:CHAR	== char "<";
	local rangle:CHAR	== char ">";
	local dot:CHAR		== char ".";
	local quote:CHAR	== char "_"";
	local spaces:List CHAR	== [space, newline, tab];

	local push!(c:CHAR, port:TEXT, t:Token):Token == { push!(c, port); t; }
					
	-- skips all newlines, return next char
	local skipnewlines!(port:TEXT):CHAR == {
		c:CHAR := newline;
		while c = newline repeat c := read! port;
		c;
	}

	-- skips all spaces and newlines, return next char
	local skipspaces!(port:TEXT):CHAR == {
		c:CHAR := newline;
		while member?(c, spaces) repeat c := read! port;
		c;
	}

	-- state = starting point
	scan!(port:TEXT):Token == {
		import from TOKEN, CHAR, List CHAR, Partial Token;
		c := skipspaces! port;
		TRACE("scanner::scan!: c = ", c);
		c = eof => token TOK__EOF;
		-- hack for parsing sumit-generated tex { => (  } => )
		c = lcurly => retract token lpar;
		c = rcurly => retract token rpar;
		c = star => scan4 port;
		c = slash => scan5 port;
		c = bslash => scan7 port;
		c = langle => scan10 port;
		c = rangle => scan11 port;
		c = quote => scan12(port, empty);
		failed?(u := token c) => {
			TRACE("scanner::scan!: ord c = ", ord c);
			letter? c => scan1(port, [c]);
			digit? c => scan2(port, [c]);
			c = colon => scan3 port;
			token TOK__UNKNOWN;
		}
		retract u;
	}

	-- state1 = scanning a name
	local scan1(port:TEXT, l:List CHAR):Token == {
		TRACE("scan1: ", l);
		c := skipnewlines! port;
		digit? c or letter? c => scan1(port, cons(c, l));
		push!(c, port, name l);
	}

	-- state2 = scanning integer or float constant
	local scan2(port:TEXT, l:List CHAR):Token == {
		TRACE("scan2: ", l);
		digit?(c := skipnewlines! port) => scan2(port, cons(c, l));
		c = dot => scan9(port, l, empty);
		c = space => integer l;
		push!(c, port, integer l);
	}

	-- state3 = scanning assigment operator
	local scan3(port:TEXT):Token == {
		import from TOKEN;
		(c := read! port) = equal => token ExpressionTreeAssign;
		push!(c, port, token TOK__UNKNOWN);
	}

	-- state4 = scanning * or **, which is equivalent to ^
	local scan4(port:TEXT):Token == {
		import from TOKEN;
		(c := read! port) = star => token ExpressionTreeExpt;
		push!(c, port, token ExpressionTreeTimes);
	}

	-- state5 = scanning / or /*, which introduces a comment
	local scan5(port:TEXT):Token == {
		import from TOKEN;
		(c := read! port) = star => scan6 port;
		push!(c, port, token ExpressionTreeQuotient);
	}

	-- state6 = inside a comment, reads until */ included
	local scan6(port:TEXT):Token == {
		import from TOKEN, CHAR;
		c := skipspaces! port;
		while c ~= eof repeat {
			if c = star then {
				(c := read! port) = slash => return scan! port;
			}
			else c := skipspaces! port;
		}
		token TOK__EOF;
	}

	-- state7 = scanning \ converts \, to *
	-- hack for reading in tex generated by sumit
	local scan7(port:TEXT):Token == {
		import from TOKEN, List CHAR, Partial Token;
		(c := skipnewlines! port) = comma => token ExpressionTreeTimes;
		letter? c => scan8(port, [c]);
		failed?(u := token bslash) => token TOK__UNKNOWN;
		push!(c, port, retract u);
	}

	-- state8 = scanning a name following a \
	-- recognizes \over, \left( and \right), drops the \ otherwise
	-- hack for reading in tex generated by sumit
	local scan8(port:TEXT, l:List CHAR):Token == {
		import from Partial Token;
		TRACE("scan8: ", l);
		c := skipnewlines! port;
		digit? c or letter? c => scan8(port, cons(c, l));
		(s := stringrev l) = "over" =>
			push!(c, port, token ExpressionTreeQuotient);
		(c = lpar and s = "left") or (c = rpar and s = "right") =>
								retract token c;
		push!(c, port, name l);
	}

	-- state9 = scanning a float constant, after the decimal point
	local scan9(port:TEXT, before:List CHAR, l:List CHAR):Token == {
		TRACE("scan9: ", before);
		TRACE("decimal part = ", l);
		digit?(c := skipnewlines! port) => scan9(port,before,cons(c,l));
		c = space => float(before, l);
		push!(c, port, float(before, l));
	}

	local stringrev(l:List CHAR):String == {
		import from MachineInteger;
		s:String := new(n := #l);
		for c in l repeat {
			s.n := c;
			n := prev n;
		}
		s;
	}

	-- state10 = scanning < or <=
	local scan10(port:TEXT):Token == {
		import from TOKEN;
		(c := read! port) = equal => token ExpressionTreeLessEqual;
		push!(c, port, token ExpressionTreeLessThan);
	}

	-- state11 = scanning > or >=
	local scan11(port:TEXT):Token == {
		import from TOKEN;
		(c := read! port) = equal => token ExpressionTreeGreaterEqual;
		push!(c, port, token ExpressionTreeGreaterThan);
	}

	-- state12 = scanning a string
	local scan12(port:TEXT, l:List CHAR):Token == {
		TRACE("scan12: ", l);
		c := read! port;
		c = quote => string l;
		scan12(port, cons(c, l));
	}
}
