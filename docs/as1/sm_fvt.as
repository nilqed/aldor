------------------------------------------------------------------------------
--
-- sm_fvt.as: A basic categoty for multivariate polynomial variables.
--
------------------------------------------------------------------------------
--  Copyright (c) 1990-2007 Aldor Software Organization Ltd (Aldor.org).
-- Copyright: INRIA, UWO and University of Lille I, 2001
-- Copyright: Marc Moreno Maza
--------------------------------------------------------------------------------

#include "algebra"

+++ `FiniteVariableType' is a category for multivariate polynomial variables
+++ that belong to a finite set.
+++ Author: Marc Moreno Maza
+++ Date Created: 09/07/01
+++ Date Last Update: 09/07/01

define FiniteVariableType: Category == VariableType with {
        variable: MachineInteger -> %;
          ++ `variable(n)' returns the `n'-th variable of the type.
        index: % -> MachineInteger;
          ++ `index(x)' returns the index of the `x' in `t'.
        #:  MachineInteger;
          ++ `#' returns the number of elements of the type.
        max: %;
          ++ `max' is the greatest variable of the type.
        min: %;
          ++ `min' is the smallest variable of the type.
        minToMax: List %;
          ++ `minToMax' returns the list of the variables of the
          ++ type sorted in increasing order.
        maxToMin: List %;
          ++ `maxToMin' returns the list of the variables of the
          ++ type sorted in decreasing order.
}







