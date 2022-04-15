------------------------------------------------------------------------------
--
-- sm_listovar.as: A basic constructor for sets of ordered variables
--
------------------------------------------------------------------------------
--  Copyright (c) 1990-2007 Aldor Software Organization Ltd (Aldor.org).
-- Copyright: INRIA, UWO and University of Lille I, 2001
-- Copyright: Marc Moreno Maza
--------------------------------------------------------------------------------

#include "algebra"

+++ `OrderedVariableList(t)' creates a finite ordered set of variables 
+++ from a list of symbols.
+++ The first element in the list is the biggest variable in the domain.
+++ Author: Marc Moreno Maza
+++ Date Created: 09/07/01
+++ Date Last Update: 09/07/01

OrderedVariableList(t:List Symbol): FiniteVariableType with {

} == MachineInteger add {

        Rep == MachineInteger;

        local nvars: MachineInteger == {
		import from List Symbol;
		assert(not empty? t);
		#t;
	}
        variable(n: MachineInteger): % == {
	     import from MachineInteger;
             assert(1 <= n);
             assert(n <= nvars);
             per n;
        }
        variable(s: Symbol): Partial(%) == {
             import from Symbol, Partial(%), List(Symbol);
             n: MachineInteger := 1;
             for v in t repeat {
                 if s = v then return [per n];
                 n := n + 1;
             }
             return failed;
        }
        symbol(x: %): Symbol == t.(rep x);
        
        {#: MachineInteger} == nvars;

        index(x: %): MachineInteger == rep(x); 

	max: % == per 1;

	min: % == per nvars;

        minToMax: List(%) == {
             import from List(%);
             reverse [per i for i in 1..nvars];
        }

        maxToMin: List(%) == {
             import from List(%);
             [per i for i in 1..nvars];
        }
        -- WARNING: DO NOT REMOVE ANY OF THE FOUR DEFINITIONS
	(x: %) > (y: %): Boolean == rep x < rep y; 

	(x: %) < (y: %): Boolean == rep x > rep y;

	(x: %) >= (y: %): Boolean == rep x <= rep y;

	(x: %) <= (y: %): Boolean == rep x >= rep y;

        extree(v:%):ExpressionTree == {
              import from Symbol, List(Symbol);
              i: MachineInteger := rep v;
              extree t.i;
        }
        (port:TextWriter) << (v:%):TextWriter == {
                        import from ExpressionTree;
                        -- tex(port, extree v);
                        infix(port, extree v);
        }
        eval(l: ExpressionTreeLeaf): Partial % == {
            TRACE("OV::eval, l = ", l);
            import from Symbol;
            symbol? l => {
                x := symbol l;
                for i in 1..nvars repeat { x = t.i => {
                        TRACE("OV::eval, returning ", variable i);
			return [variable i];
	        } }
                failed;
            }
            failed;
        }
}












