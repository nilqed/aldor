------------------------------   sit_OPless.as   ------------------------------
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

	NOTYET(a,b) == p << a << " output for " << b << " not yet implemented.";
}

   
ExpressionTreeLessEqual: ExpressionTreeOperator == add
{
	import from String, TREE;

	name:Symbol             == -"<=";
	arity:SI                == 2;
	uniqueId:SI             == UID__LESSEQUAL;
	texParen?(p:SI):Boolean == true;

	aldor  (p:TEXT, l:List TREE): TEXT == INFIX2(aldor,p,l,"<=");
	axiom   (p:TEXT, l:List TREE): TEXT == INFIX2(axiom,p,l,"<=");
	C       (p:TEXT, l:List TREE): TEXT == NOTYET("C","<=");
	fortran (p:TEXT, l:List TREE): TEXT == NOTYET("fortran","<=");
	maple   (p:TEXT, l:List TREE): TEXT == INFIX2(maple,p,l,"<=");
	tex     (p:TEXT, l:List TREE): TEXT == INFIX2(tex,p,l,"\le ");
	infix   (p:TEXT, l:List TREE): TEXT == INFIX2(infix,p,l," <= ");
	lisp	(p:TEXT, l:List TREE): TEXT == NOTYET("lisp", "<=");
}


ExpressionTreeLessThan: ExpressionTreeOperator == add
{
	import from String, TREE;

	name:Symbol             == -"<";
	arity:SI                == 2;
	uniqueId:SI             == UID__LESSTHAN;
	texParen?(p:SI):Boolean == true;

	aldor  (p:TEXT, l:List TREE): TEXT == INFIX2(aldor,p,l,"<");
	axiom   (p:TEXT, l:List TREE): TEXT == INFIX2(axiom,p,l,"<");
	C       (p:TEXT, l:List TREE): TEXT == NOTYET("C","<");
	fortran (p:TEXT, l:List TREE): TEXT == NOTYET("fortran","<");
	maple   (p:TEXT, l:List TREE): TEXT == INFIX2(maple,p,l,"<");
	tex     (p:TEXT, l:List TREE): TEXT == INFIX2(tex,p,l,"<");
	lisp	(p:TEXT, l:List TREE): TEXT == NOTYET("lisp", "<");
}
