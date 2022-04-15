------------------------------   sit_OPand.as   ------------------------------
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
	FALSE == (t:TREE):Boolean +-> false;
	TRUE == (t:TREE):Boolean +-> true;
}


ExpressionTreeAnd: ExpressionTreeOperator == add
{
	import from String, TREE, ExpressionTreeOperatorTools;

	name:Symbol             == -"and";
	arity:SI                == -1;
	uniqueId:SI             == UID__AND;
	texParen?(p:SI):Boolean == true;

	aldor  (p:TEXT, l:List TREE): TEXT == infix (p,l,TRUE,aldor," and ");
	axiom   (p:TEXT, l:List TREE): TEXT == infix (p,l,TRUE,axiom," and ");
	C       (p:TEXT, l:List TREE): TEXT == infix (p,l,TRUE,C, "&");
	fortran (p:TEXT, l:List TREE): TEXT == NOTYET("fortran",name);
	maple   (p:TEXT, l:List TREE): TEXT == infix (p,l,TRUE,maple," and ");
	tex     (p:TEXT, l:List TREE): TEXT == infix (p,l,TRUE,tex," \wedge ");
	infix   (p:TEXT, l:List TREE): TEXT == infix (p,l,TRUE,infix," /\ ");
}
