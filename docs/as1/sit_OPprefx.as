-----------------------------   sit_OPprefx.as   ------------------------------
-- Copyright (c) Manuel Bronstein 1995
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
}


ExpressionTreePrefix(s:Symbol): ExpressionTreeOperator == add {
	import from String, TREE, ExpressionTreeOperatorTools;

	name:Symbol             == s;
	local sname:String	== name s;
	local texname:String	== "\" + sname;
	arity:SI                == -1;
	uniqueId:SI             == UID__PREFIX;
	texParen?(p:SI):Boolean == false;

	aldor(p:TEXT, l:List TREE):TEXT		== prefix(p, l, aldor, sname);
	axiom(p:TEXT, l:List TREE):TEXT		== prefix(p, l, axiom, sname);
	C(p:TEXT, l:List TREE):TEXT		== prefix(p, l, C, sname);
	fortran(p:TEXT, l:List TREE):TEXT	== prefix(p, l, fortran, sname);
	maple(p:TEXT, l:List TREE):TEXT		== prefix(p, l, maple, sname);

	tex(p:TEXT, l:List TREE):TEXT ==
		prefix(p, l, tex, texname, "\left(", "\right)");
}
