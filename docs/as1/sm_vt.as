------------------------------------------------------------------------------
--
-- sm_vt.as: A basic categoty for multivariate polynomial variables.
--
------------------------------------------------------------------------------
--  Copyright (c) 1990-2007 Aldor Software Organization Ltd (Aldor.org).
-- Copyright: INRIA, UWO and University of Lille I, 2001
-- Copyright: Marc Moreno Maza
--------------------------------------------------------------------------------

#include "algebra"

+++ `VariableType' is a category for multivariate polynomial variables.
+++ Variables are looked as symbols with additionnal properties such 
+++ as a total order.
+++ Author: Marc Moreno Maza
+++ Date Created: 08/07/01
+++ Date Last Update: 09/07/01

define VariableType: Category == Join(TotallyOrderedType, 
 ExpressionType, HashType, SerializableType, Parsable) 
    with { 
        variable: Symbol -> Partial(%);
          ++ `variable(s)' returns the variable associated with `s' 
          ++ if any, otherwise `failed' is returned.
        symbol: % -> Symbol;
          ++ `symbol(x)' returns the symbol associated with `x'.
}





