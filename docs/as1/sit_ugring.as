----------------------------- sit_ugring.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "algebra"


define UnivariateGcdRing: Category == GcdDomain with {
	gcdUP: (P: UnivariatePolynomialAlgebra0 %) -> (P, P) -> P;
	gcdUP!: (P: UnivariatePolynomialAlgebra0 %) -> (P, P) -> P;
	gcdquoUP: (P: UnivariatePolynomialAlgebra0 %) -> (P, P) -> (P, P, P);
	default {
		gcdUP!(P: UnivariatePolynomialAlgebra0 %):(P,P) -> P == {
			(p:P, q:P):P +-> gcdUP(P)(p, q);
		}

		gcdquoUP(P: UnivariatePolynomialAlgebra0 %):(P,P)->(P,P,P) == {
			gcdP := gcdUP P;
			(p:P, q:P):(P, P, P) +-> {
				g := gcdP(p, q);
				(g, quotient(p, g), quotient(q, g));
			}
		}
	}
}

