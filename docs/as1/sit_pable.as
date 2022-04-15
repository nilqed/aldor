----------------------------- sit_pable.as ----------------------------------
--
-- Expression Tree Arithmetic Interpreters
--
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"
#include "algebrauid"

macro {
	TREE	== ExpressionTree;
	LEAF	== ExpressionTreeLeaf;
}


define Parsable: Category == InputType with {
	eval:	TREE -> Partial %;
	eval:	LEAF -> Partial %;
	eval:	(MachineInteger, List TREE) -> Partial %;
	default {
		eval(t:TREE):Partial % == {
			TRACE("parsable::eval ", t);
			leaf? t => eval leaf t;
			evalOp t;
		}

		local evalOp(t:TREE):Partial % == {
			import from Boolean;
			TRACE("parsable::evalOp ", t);
			assert(~leaf? t);
			eval(uniqueId$operator(t), arguments t);
		}

		<< (port:TextReader):% == {
			import from InfixExpressionParser;
			import from Partial TREE, Partial %;
			retract eval retract parse! parser port;
		}
	}
}
