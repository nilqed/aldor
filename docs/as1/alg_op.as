------------------------------- alg_op.as ----------------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1994
--
-- This type must be included inside "sit_extree.as" to be compiled,
-- but is in a separate file for documentation purposes.


macro {
	Z	== MachineInteger;
	OP	== ExpressionTreeOperator;
	TEXT	== TextWriter;
	TREE	== ExpressionTree;
}

define ExpressionTreeOperator: Category == with {
	aldor:		(TEXT, List TREE) -> TEXT;
	axiom:		(TEXT, List TREE) -> TEXT;
	C:		(TEXT, List TREE) -> TEXT;
	fortran:	(TEXT, List TREE) -> TEXT;
	infix:		(TEXT, List TREE) -> TEXT;
	lisp:		(TEXT, List TREE) -> TEXT;
	maple:		(TEXT, List TREE) -> TEXT;
	tex:		(TEXT, List TREE) -> TEXT;
	arity:		Z;
	name:		Symbol;
	texParen?:	Z -> Boolean;
	uniqueId:	Z;
	default {
		infix(p:TEXT, l:List TREE):TEXT == {
			import from TREE, String, Symbol;
			p := p << name << "(";
			for arg in l repeat p := infix(p << " ", arg);
			p << ")";
		}

		lisp(p:TEXT, l:List TREE):TEXT == {
			import from TREE, String, Symbol;
			p := p << "(" << name;
			for arg in l repeat p := lisp(p << " ", arg);
			p << ")";
		}
	}
}

