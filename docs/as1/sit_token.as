------------------------------- sit_token.as ----------------------------------
--
-- Tokens for the lexical scanner
--
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "algebra"

#include "alg_tokens"

macro {
	Leaf	== ExpressionTreeLeaf;
	OP 	== ExpressionTreeOperator;
	CHAR	== Character;
	TEXT	== TextWriter;
}

#if GMP
macro FLOAT == Float;
#else
macro FLOAT == DoubleFloat;
#endif


Token: Join(OutputType, PrimitiveType) with {
	float:	(List CHAR, List CHAR) -> %;
	integer:	List CHAR -> %;
	leaf:		% -> Leaf;
	leaf?:		% -> Boolean;
	name:		List CHAR -> %;
	operator:	% -> OP;
	operator?:	% -> Boolean;
	prefix:		List CHAR -> %;
	special:	% -> TOKEN;
	special?:	% -> Boolean;
	string:		List CHAR -> %;
	token:		OP -> %;
	token:		MachineInteger -> %;
	token:		CHAR -> Partial %;
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

	-- before, after = lists of digits from low to high
	float(before:List CHAR, after:List CHAR):% == {
		import from Boolean, FLOAT;
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
	local floatValue(l:List CHAR):(FLOAT, FLOAT) == {
		import from Boolean, CHAR, String, MachineInteger;
		assert(~empty? l);
		n:FLOAT := 0;
		ten := 10::FLOAT;
		pow10:FLOAT := 1;
		ord0 := ord char "0";
		while ~empty? l repeat {
			n := n + (ord(first l) - ord0)::FLOAT * pow10;
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
