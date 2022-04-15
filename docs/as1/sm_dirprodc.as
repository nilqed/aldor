--------------------------------------------------------------------------------
--
-- sm_dirprodc.as: A category for finite cartesian (or direct) product
--                of a type.
--
--------------------------------------------------------------------------------
--  Copyright (c) 1990-2007 Aldor Software Organization Ltd (Aldor.org).
-- Copyright: INRIA, UWO, and University of Lille I, 2001
-- Copyright: Marc Moreno Maza
--------------------------------------------------------------------------------

-- cat DirectProductCategory

#include "algebra"

+++ `DirectProductCategory(dim, T)' is the category of
+++ cartesian products of `dim' copies of `T' Hence
+++ an elements of a domain of this category is a
+++ a product (or tuple) of elements from `T' with 
+++ length `dim'. The components of such a tuple
+++ are indexed from `firstIndex' to `lastIndex'.
+++ Thus `dim' is `lastIndex - firstIndex + 1'.
+++ This category is essentially designed to support the
+++ implementation of multivariate monomials involving at
+++ most `dim -1' (if one component is used for the
+++ total degree) or `dim' (if not) variables. 
+++ Author: Marc Moreno Maza
+++ Date Created: 09/07/01
+++ Date Last Update: 10/07/01

define DirectProductCategory(dim: MachineInteger, T: ExpressionType): 
 Category == Join(ExpressionType, CopyableType, LinearStructureType T) with {
        bracket: Tuple(T) -> %;
          ++ `bracket(t)' returns the product with components 
          ++ `element(t.i)'. This assumes that `t' has length 
          ++ `dim'.
        lastIndex: MachineInteger;
          ++ `lastIndex' returns `firstIndex + dim - 1'
          ++ that is the biggest index of a product.
        generator: % -> Generator(T);
          ++ `generator(x)' traverses `x' starting from the
          ++ component associated with `firstIndex'.
	map: ((T,T) -> T) -> (%, %) -> %;
	  ++ `map(f)(x, y)' returns the product with components
	  ++ `f(x.i, y.i)'.
        map: (T -> T) -> % -> %;
          ++ `map(f)(x)' returns the same as 
          ++ `[f(x.i) for i in firstIndex..dim]'.
        map!: (T -> T) -> % -> %;
          ++ `map!(f)(x)' maps `f' onto every component
          ++ of `x'. 
        default {
            extree(x: %): ExpressionTree == {
                  import from MachineInteger, T, List(ExpressionTree);
                  ExpressionTreeList [extree (x.i) for i in firstIndex..lastIndex];
            }
        }
}










