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
------------------------------- sit_token.as ----------------------------------
--
-- Tokens for the lexical scanner
--
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"
#include "tokens"

macro {
	Leaf	== ExpressionTreeLeaf;
	OP 	== ExpressionTreeOperator;
	CHAR	== Character;
	TEXT	== TextWriter;
}

#if ALDOC
\thistype{Token}
\History{Manuel Bronstein}{21/11/95}{created}
\Usage{import from \this}
\Descr{\this~is a type whose elements are parser tokens.}
\begin{exports}
\category{\astype{OutputType}}\\
\category{\astype{PrimitiveType}}\\
\asexp{float}:
& (\astype{List} \astype{Character}, \astype{List} \astype{Character}) $\to$ \% & Create a float token\\
\asexp{integer}:
& \astype{List} \astype{Character} $\to$ \% & Create an integer token\\
\asexp{leaf}: &	\% $\to$ \astype{ExpressionTreeLeaf} & Conversion to a leaf\\
\asexp{leaf?}: & \% $\to$ \astype{Boolean} & Test for a leaf\\
\asexp{name}:
& \astype{List} \astype{Character} $\to$ \% & Create a constant name token\\
\asexp{operator}:
& \% $\to$ \astype{ExpressionTreeOperator} & Conversion to an operator\\
\asexp{operator?}: & \% $\to$ \astype{Boolean} & Test for an operator\\
\asexp{prefix}:
& \astype{List} \astype{Character} $\to$ \% & Create a prefix function token\\
\asexp{special}:
& \% $\to$ \astype{MachineInteger} & Conversion to a special token\\
\asexp{special?}: & \% $\to$ \astype{Boolean} & Test for a special token\\
\asexp{string}: & \astype{List} \astype{Character} $\to$ \% & Create a string\\
\asexp{token}: & \astype{Character} $\to$ \astype{Partial} \% &
Create a single character token\\
\end{exports}
#endif

Token: Join(OutputType, PrimitiveType) with {
	float:	(List CHAR, List CHAR) -> %;
#if ALDOC
\aspage{float}
\Usage{\name($l_1,l_2$)}
\Signature{(\astype{List} \astype{Character}, \astype{List} \astype{Character})}{\%}
\Params{
$[d_0,\dots,d_n]$ & \astype{List} \astype{Character} & A list of digits\\
$[e_0,\dots,e_m]$ & \astype{List} \astype{Character} & A list of digits\\
}
\Retval{\name($[d_0,\dots,d_n], [e_0,\dots,e_m]$) returns the float
$d_n d_{n-1} \dots d_0 . e_m e_{m-1} \dots e_0$ as a token.}
\seealso{\asexp{integer}}
#endif
	integer:	List CHAR -> %;
#if ALDOC
\aspage{integer}
\Usage{\name~l}
\Signature{\astype{List} \astype{Character}}{\%}
\Params{
$[d_0,\dots,d_n]$ & \astype{List} \astype{Character} & A list of digits\\ }
\Retval{\name($[d_0,\dots,d_n]$) returns the integer
$d_0 + 10 d_1 + \dots + 10^n d_n$ as a token.}
\seealso{\asexp{float}}
#endif
	leaf:		% -> Leaf;
	leaf?:		% -> Boolean;
#if ALDOC
\aspage{leaf}
\astarget{\name?}
\Usage{ \name~t\\ \name?~t }
\Signatures{
\name: & \% $\to$ \astype{ExpressionTreeLeaf}\\
\name?: & \% $\to$ \astype{Boolean}\\
}
\Params{ {\em t} & \% & A token\\ }
\Retval{
\name~a returns $a$ as a leaf is $a$ is a leaf.
\name?~a returns \true~if a is a leaf, \false~otherwise.
}
\seealso{\asexp{operator}, \asexp{special}}
#endif
	name:		List CHAR -> %;
#if ALDOC
\aspage{name}
\Usage{\name~l}
\Signature{\astype{List} \astype{Character}}{\%}
\Params{
$[c_0,\dots,c_n]$ & \astype{List} \astype{Character} & A list of characters\\ }
\Retval{\name($[c_0,\dots,c_n]$) returns the name $c_n c_{n-1} \dots c_0$
as a token representing a constant symbol.}
\seealso{\asexp{prefix}, \asexp{string}}
#endif
	operator:	% -> OP;
	operator?:	% -> Boolean;
#if ALDOC
\aspage{operator}
\astarget{\name?}
\Usage{ \name~t\\ \name?~t }
\Signatures{
\name: & \% $\to$ \astype{ExpressionTreeOperator}\\
\name?: & \% $\to$ \astype{Boolean}\\
}
\Params{ {\em t} & \% & A token\\ }
\Retval{
\name~a returns $a$ as an operator is $a$ is an operator.
\name?~a returns \true~if a is an operator, \false~otherwise.
}
\seealso{\asexp{leaf}, \asexp{special}}
#endif
	prefix:		List CHAR -> %;
#if ALDOC
\aspage{prefix}
\Usage{\name~l}
\Signature{\astype{List} \astype{Character}}{\%}
\Params{
$[c_0,\dots,c_n]$ & \astype{List} \astype{Character} & A list of characters\\ }
\Retval{\name($[c_0,\dots,c_n]$) returns the name $``c_n c_{n-1} \dots c_0''$
as a token representing a prefix function.}
\seealso{\asexp{name}}
#endif
	special:	% -> TOKEN;
	special?:	% -> Boolean;
#if ALDOC
\aspage{special}
\astarget{\name?}
\Usage{ \name~t\\ \name?~t }
\Signatures{
\name: & \% $\to$ \astype{MachineInteger}\\
\name?: & \% $\to$ \astype{Boolean}\\
}
\Params{ {\em t} & \% & A token\\ }
\Retval{
\name~a returns $a$ as a special token is $a$ is a special token.
\name?~a returns \true~if a is a special token, \false~otherwise.
}
\seealso{\asexp{leaf}, \asexp{special}}
#endif
	string:		List CHAR -> %;
#if ALDOC
\aspage{name}
\Usage{\name~l}
\Signature{\astype{List} \astype{Character}}{\%}
\Params{
$[c_0,\dots,c_n]$ & \astype{List} \astype{Character} & A list of characters\\ }
\Retval{\name($[c_0,\dots,c_n]$) returns the string $``c_n c_{n-1} \dots c_0''$
as a token representing a constant.}
\seealso{\asexp{name}, \asexp{prefix}}
#endif
	token:		OP -> %;
	token:		MachineInteger -> %;
	token:		CHAR -> Partial %;
#if ALDOC
\aspage{token}
\Usage{\name~a}
\Signatures{
\name: & \astype{Character} $\to$ \astype{Partial} \%\\
\name: & \astype{ExpressionTreeOperator} $\to$ \astype{Partial} \%\\
\name: & \astype{MachineInteger} $\to$ \astype{Partial} \%\\
}
\Params{
{\em a} & \astype{Character} & A single character token\\
        & \astype{ExpressionTreeOperator} & An operator\\
        & \astype{MachineInteger} & A code of a special token\\
}
\Retval{Returns the token corresponding to the single character $a$,
\failed if there is none.}
#endif
} == add {
	Rep == Union(uleaf: Leaf, uop: OP, utok: TOKEN);

	import from Rep;

	sample:%			== per [TOK__EOF];
	leaf?(t:%):Boolean		== rep(t) case uleaf;
	leaf(t:%):Leaf			== { assert(leaf? t); rep(t).uleaf; }
	operator?(t:%):Boolean		== rep(t) case uop;
	operator(t:%):OP		== { assert(operator? t); rep(t).uop; }
	special?(t:%):Boolean		== rep(t) case utok;
	special(t:%):TOKEN		== { assert(special? t); rep(t).utok; }
	token(n:MachineInteger):%	== per [n];
	token(op:OP):%			== per [op];
	local token(l:Leaf):%		== per [l];
	string(l:List CHAR):%		== token leaf revstring l;
	name(l:List CHAR):%		== token leaf symbol l;
	prefix(l:List CHAR):%		== token ExpressionTreePrefix symbol l;

	local opout(p:TEXT, t:%):TEXT == {
		import from Symbol;
		p << name$operator(t);
	}

	local opeq(t:%, s:%):Boolean == {
		import from MachineInteger;
		uniqueId$operator(t) = uniqueId$operator(s);
	}

	(p:TEXT) << (t:%):TEXT == {
		leaf? t => p << leaf t;
		operator? t => opout(p, t);  -- TEMPORARY (BUG 911)
		p << special t;
	}

	(x:%) = (y:%):Boolean == {
		leaf? x => leaf? y and leaf x = leaf y;
		special? x => special? y and special x = special y;
		operator? x and operator? y and opeq(x, y) -- TEMPORARY (911)
	}

	token(c:CHAR):Partial % == {
		import from String;
		c = char "^" => [token ExpressionTreeExpt];
		c = char "-" => [token ExpressionTreeMinus];
		c = char "+" => [token ExpressionTreePlus];
		c = char "/" => [token ExpressionTreeQuotient];
		c = char "*" => [token ExpressionTreeTimes];
		c = char "(" => [token TOK__LPAREN];
		c = char ")" => [token TOK__RPAREN];
		c = char "[" => [token TOK__LBRACKET];
		c = char "]" => [token TOK__RBRACKET];
		c = char "{" => [token TOK__LCURLY];
		c = char "}" => [token TOK__RCURLY];
		c = char ";" => [token TOK__EOEXPR];
		c = char "," => [token TOK__COMMA];
		failed;
	}

	-- l = list of digits from low to high
	integer(l:List CHAR):% == {
		import from Boolean;
		assert(~empty? l);
		(n, e) := integerValue l;
		token leaf n;
	}

	-- before, after = lists of digits from low to high
	float(before:List CHAR, after:List CHAR):% == {
		import from Boolean, Float;
		assert(~empty? before);
		(x, e) := floatValue before;
		if ~empty?(after) then {
			(m, e) := floatValue after;
			x := x + (m / e);
		}
		token leaf x;
	}

	-- l = list of digits from low to high
	-- returns (n, e) where n is the value of l
	-- and e = 10^m such that 10^{m-1} <= n < 10^m
	integerValue(l:List CHAR):(Integer, Integer) == {
		import from Boolean, CHAR, String, MachineInteger;
		assert(~empty? l);
		n:Integer := 0;
		pow10:Integer := 1;
		ord0 := ord char "0";
		while ~empty? l repeat {
			n := n + (ord(first l) - ord0)::Integer * pow10;
			pow10 := 10 * pow10;
			l := rest l;
		}
		(n, pow10);
	}

	-- l = list of digits from low to high
	-- returns (n, e) where n is the value of l
	-- and e = 10^m such that 10^{m-1} <= n < 10^m
	local floatValue(l:List CHAR):(Float, Float) == {
		import from Boolean, CHAR, String, MachineInteger;
		assert(~empty? l);
		n:Float := 0;
		ten := 10::Float;
		pow10:Float := 1;
		ord0 := ord char "0";
		while ~empty? l repeat {
			n := n + (ord(first l) - ord0)::Float * pow10;
			pow10 := ten * pow10;
			l := rest l;
		}
		(n, pow10);
	}

	-- l = list of chars from right to left
	local symbol(l:List CHAR):Symbol == - revstring l;
	local revstring(l:List CHAR):String == {
		import from Boolean, MachineInteger, CHAR;
		assert(~empty? l);
		a:String := new(n := #l, null);
		for i in 1..n repeat {
			a(n-i) := first l;
			l := rest l;
		}
		a;
	}
}
