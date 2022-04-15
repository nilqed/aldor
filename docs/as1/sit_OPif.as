------------------------------   sit_OPif.as   ------------------------------
-- Copyright (c) Marco Codutti 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "algebra"
#include "algebrauid"

macro {
	TEXT == TextWriter;
	TREE == ExpressionTree;
	SI   == MachineInteger;

	NOTYET(a,b) == p << a << " output for " << b << " not yet implemented.";
}


ExpressionTreeIf: ExpressionTreeOperator == add
{
	import from String, TREE,ExpressionTreeOperatorTools,ExpressionTreeLeaf;

	name:Symbol             == -"if";
	arity:SI                == 2;
	uniqueId:SI             == UID__IF;
	texParen?(p:SI):Boolean == true;

	aldor (p:TEXT, l:List TREE): TEXT == prefix(p,l,aldor,"__if");
	axiom (p:TEXT, l:List TREE): TEXT == prefix(p,l,axiom,"__if"); 

	C (p:TEXT, l:List TREE): TEXT == 
	{
		p << "if (";
		if leaf? l.2 and string? (s := leaf(l.2)) then
		if string s = "always" then p << "1" else p << "0";
					else C (p,l.2);
		p << ") {";
		C (p,l.1);
		p << "}";
	}

	fortran (p:TEXT, l:List TREE): TEXT == NOTYET("fortran","if");
	lisp (p:TEXT, l:List TREE): TEXT == NOTYET("lisp","if");

	maple (p:TEXT, l:List TREE): TEXT == 
	{
		p << "if "; 
		if leaf? l.2 and string? (s := leaf(l.2)) then
		if string s = "always" then p << "true" else p << "false";
		else maple (p,l.2);
		p << "then ";
		maple (p,l.1);
		p << "fi";
	}

	tex (p:TEXT, l:List TREE): TEXT ==
	{
		tex (p,l.2);
		p << "\quad ";
		if leaf? l.1 and string? (s := leaf(l.1)) and string s = "never"
		then p << string s;
		else { p << "\quad \mbox{if }"; tex (p,l.1)};
	}
}
