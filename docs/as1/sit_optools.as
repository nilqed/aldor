-------------------------- sit_optools.as --------------------------
--
-- Tools for generic operator methods
--
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "algebra"


macro {
	TEXT	== TextWriter;
	TREE 	== ExpressionTree;
}

ExpressionTreeOperatorTools: with {
	infix: (TEXT, List TREE, TREE -> Boolean, (TEXT, TREE) -> TEXT,
		String, lp:String == "(", rp:String == ")") -> TEXT;
	lisp: (TEXT, String, List TREE) -> TEXT;
	prefix: (TEXT, TREE, TREE -> Boolean, (TEXT, TREE) -> TEXT,
		String, lp:String == "(", rp:String == ")") -> TEXT;
	prefix: (TEXT, List TREE, (TEXT, TREE) -> TEXT,
		String, lp:String == "(", rp:String == ")") -> TEXT;
} == add {
	import from MachineInteger;

	local alwaysTrue(t:TREE):Boolean == true;

        prefix(p:TEXT, t:TREE, par?:TREE -> Boolean, f:(TEXT,TREE) -> TEXT,
		op:String, lp:String, rp:String):TEXT == {
			p := p << op;
			paren? := par? t;
			if paren? then p := p << lp;
			p := f(p, t);
			paren? => p << rp;
			p;
	}

        prefix(p:TEXT, l:List TREE, f:(TEXT,TREE) -> TEXT,
		op:String, lp:String, rp:String):TEXT == {
			p := p << op << lp;
			for t in l for i in #l.. by -1 repeat {
				p := f(p, t);
				if i > 1 then p := p << ",";
			}
			p << rp;
	}

        infix(p:TEXT, l:List TREE, par?:TREE -> Boolean, f:(TEXT,TREE) -> TEXT,
		op:String, lp:String, rp:String):TEXT == {
			empty? l => p;
			empty? rest l => f(p, first l);
			paren? := par? first l;
			if paren? then p := p << lp;
			p := f(p, first l);
			for t in rest l repeat {
				if paren? then p := p << rp;
				p := p << op;
				paren? := par? t;
				if paren? then p := p << lp;
				p := f(p, t);
			}
			paren? => p << rp;
			p;
	}

	lisp(p:TEXT, s:String, l:List TREE):TEXT == {
		import from TREE;
		p := p << "(" << s;
		for arg in l repeat p := lisp(p << " ", arg);
		p << ")";
	}
}
