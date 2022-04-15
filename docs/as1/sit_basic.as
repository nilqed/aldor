------------------------------- sit_basic.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

-- Boolean is extended in this file, so don't import it
#assert DoNotImportBoolean

#include "algebra"
#include "algebrauid"

macro {
	Z == MachineInteger;
	TREE == ExpressionTree;
	LEAF == ExpressionTreeLeaf;
}


define ExpressionType: Category == Join(OutputType, PrimitiveType) with {
	extree: % -> TREE;
	relativeSize: % -> MachineInteger;
	default {
		relativeSize(x:%):MachineInteger == 1;

		(port:TextWriter) << (a:%):TextWriter == {
			import from TREE;
			-- tex(port, extree a);
			infix(port, extree a);
		}
	}
}

extend Boolean: Join(Parsable, ExpressionType) == add {
	extree(x:%):TREE == {
		import from LEAF;
		extree leaf(x);
	}

	eval(t:LEAF):Partial % == {
		boolean? t => [boolean t];
		failed;
	}

	eval(op:Z, args:List TREE):Partial % == {
		local u:Partial %;
		op = UID__AND => {
			empty? args or failed?(u := eval first args) => failed;
			ans? := retract u;
			for arg in rest args while ans? repeat {
				failed?(u := eval arg) => return failed;
				ans? := retract u;
			}
			[ans?];
		}
		op = UID__OR => {
			empty? args or failed?(u := eval first args) => failed;
			ans? := retract u;
			for arg in rest args while(~ans?) repeat {
				failed?(u := eval arg) => return failed;
				ans? := retract u;
			}
			[ans?];
		}
		op = UID__NOT => {
			empty? args or ~empty?(rest args)
				or failed?(u := eval first args) => failed;
			[~retract u];
		}
		failed;
	}
}

extend String: Join(Parsable, ExpressionType) == add {
	relativeSize(x:%):MachineInteger == #x;

	extree(x:%):TREE == {
		import from LEAF;
		extree leaf(x);
	}

	eval(t:LEAF):Partial % == {
		import from Symbol;
		string? t => [string t];
		symbol? t => [name symbol t];
		failed;
	}

	eval(op:Z, args:List TREE):Partial % == {
		op = UID__PLUS => {
			ans:% := empty;
			for arg in args repeat {
				u := eval(arg)@Partial(%);
				failed? u => return failed;
				ans := ans + retract u;
			}
			[ans];
		}
		failed;
	}
}

extend Symbol: Join(Parsable, ExpressionType) == add {
	extree(x:%):TREE == {
		import from LEAF;
		extree leaf(x);
	}

	eval(t:LEAF):Partial % == {
		string? t => [- string t];
		symbol? t => [symbol t];
		failed;
	}

	eval(op:Z, args:List TREE):Partial % == {
		import from Boolean, String, Partial String;
		op = UID__PLUS => {
			ans:String := empty;
			for arg in args repeat {
				u := eval(arg)@Partial(String);
				failed? u => return failed;
				ans := ans + retract u;
			}
			[-ans];
		}
		op = UID__MINUS => {
			empty? args or ~empty?(rest args)
				or failed?(u:=eval first(args)@Partial(String))
					=> failed;
			[- retract u];
		}
		failed;
	}
}

