------------------------------------------------------------------------------
--
-- rmpzx.as: A basic constructor for Recursive Multivariate Polynomials
--
------------------------------------------------------------------------------
-- Copyright (c) Marc Moreno Maza
-- Copyright (c) 1990-2007 Aldor Software Organization Ltd (Aldor.org).
-- Copyright (c) INRIA (France), USTL (France), UWO (Ontario) 2002
------------------------------------------------------------------------------

#include "algebra"

macro { 
        Z == Integer;
        SUP == SparseUnivariatePolynomial;
}

SparseIntegerMultivariatePolynomial(V: VariableType):
-- Join(Parsable,Algebra Integer,CommutativeRing,CopyableType)
   RecursiveMultivariatePolynomialCategory0(Z, V) with {
      univariate: % -> SUP(%);
        ++ `univariate(p)' returns `p' as a univariate polynomial
        ++ w.r.t. its main variable.
      multivariate: (SUP(%), V) -> %;
        ++ `multivariate(p,v)' returns `p' as a multivariate 
        ++ polynomial whose main variable is `v'. An error
        ++ is raised if one coeffcient of `p' does not have
        ++ degree zero w.r.t. `v'. 
} == RecursiveMultivariatePolynomial0(SUP, Z, V) add { }



