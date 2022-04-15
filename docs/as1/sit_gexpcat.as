------------------------------- sit_gexpcat.as ------------------------------
--
-- gec.as: A basic category for monomial domains looked as addtive monoids.
--
--  Copyright (c) 1990-2007 Aldor Software Organization Ltd (Aldor.org).
-- Copyright: INRIA, UWO and University of Lille I, 2001
-- Copyright: Marc Moreno Maza
------------------------------------------------------------------------------

#include "algebra"


define GeneralExponentCategory: Category ==
	Join(TotallyOrderedType, ExpressionType) with {
        0: %;
        +: (%, %) -> %;
        add!: (%, %) -> %;
        zero?: % -> Boolean;
	cancel: (%, %) -> %; 
        cancel?: (%, %) -> Boolean;
	cancelIfCan: (%, %) -> Partial %;
        times: (Integer, %) -> %;
}

extend MachineInteger: Join(Parsable, GeneralExponentCategory) == add {
	relativeSize(x:%):MachineInteger== abs x;
	cancel?(x:%, y:%):Boolean	== x >= y;
	cancel(x:%, y:%):%		== x - y;
	cancelIfCan(x:%, y:%):Partial %	== { x < y => failed; [x - y] }

	extree(x:%):ExpressionTree == {
		import from ExpressionTreeLeaf;
		extree leaf(x);
	}

	eval(t:ExpressionTreeLeaf):Partial % == {
		import from Integer;
		machineInteger? t => [machineInteger t];
		integer? t => [machine integer t];
		failed;
	}

	eval(op:MachineInteger, args:List ExpressionTree):Partial % == {
		import from ParsingTools %;
		evalArith(op, args);
	}

	times(n:Integer, x:%):% == {
		zero? x => x;
		machine(n) * x;
	}

}

