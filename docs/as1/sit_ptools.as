----------------------------- sit_ptools.as ----------------------------------
--
-- This file provides help-functions for parsing expression trees
--
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"
#include "algebrauid"

macro {
	TREE == ExpressionTree;
	LEAF == ExpressionTreeLeaf;
}


ParsingTools(R:Join(Parsable, ArithmeticType)): with {
	evalArith: (MachineInteger, List TREE) -> Partial R;
	evalInt: TREE -> Partial Integer;
} == add {
	macro intdom?	== R has IntegralDomain;
	macro float?	== R has FloatType;
	local maxint:Integer	== (max$MachineInteger)::Integer;

	evalInt(t:TREE):Partial Integer == {
		import from Integer, LEAF;
		leaf? t => {
			l := leaf t;
			machineInteger? l => [machineInteger(l)::Integer];
			integer? l => [integer l];
			failed;
		}
		failed;
	}

	evalArith(op:MachineInteger, l:List TREE):Partial R == {
		import from Boolean, Partial Integer;
		TRACE("parsable::eval:op = ", op);
		TRACE("parsable::eval:l = ", l);
		op = UID__PLUS => {
			ans:R := 0;
			for arg in l repeat {
				u := eval(arg)$R;
				failed? u => return failed;
				ans := ans + retract u;
			}
			[ans];
		}
		op = UID__TIMES => {
			ans:R := 1;
			for arg in l repeat {
				u := eval(arg)$R;
				failed? u => return failed;
				ans := ans * retract u;
			}
			[ans];
		}
		op = UID__MINUS => {
			assert(#l = 1 or #l = 2);
			failed?(u := eval(first l)$R) => failed;
			empty? rest l => [- retract u];
			failed?(v := eval(first rest l)$R) => failed;
			[retract(u) - retract(v)];
		}
		op = UID__EXPT => {
			assert(#l = 2);
			failed?(u := eval(first l)$R)
				or failed?(w := evalInt first rest l)
				or (e := retract w) < 0 or e > maxint => failed;
			[retract(u)^machine(e)];
		}
		intdom? and op = UID__DIVIDE => {
			assert(#l = 2);
			failed?(u := eval(first l)$R)
				or failed?(v := eval(first rest l)$R) => failed;
			zero?(vv := retract v) => throw SyntaxException;
			exactQuotient(retract u, vv)$R;
		}
		float? and op = UID__DIVIDE => {
			assert(#l = 2);
			failed?(u := eval(first l)$R)
				or failed?(v := eval(first rest l)$R) => failed;
			zero?(vv := retract v) => throw SyntaxException;
			[retract(u) / vv];
		}
		failed;
	}
}

