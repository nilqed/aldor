----------------------------- sit_fring.as --------------------------------
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"

macro {
	Z == Integer;
	FR == FractionalRoot;
	POL == UnivariatePolynomialAlgebra0;
}


define FactorizationRing:Category== Join(GcdDomain, RationalRootRing) with {
	factor: (P:POL %) -> P -> (%, Product P);
	fractionalRoots: (P:POL %) -> P -> Generator FR %;
	roots: (P:POL %) -> P -> Generator FR %;
	default {
		roots(P:POL %):P -> Generator FR % == {
			froots := fractionalRoots P;
			(p:P):Generator FR % +-> generate {
				import from FR %;
				for z in froots p | integral? z repeat yield z;
			}
		}

		fractionalRoots(P:POL %):P -> Generator FR % == {
			fact := factor P;
			(p:P):Generator FR % +-> generate {
				import from Z, FR %, Product P;
				(c, fp) := fact p;
				for term in fp repeat {
					(q, n) := term;
					if one? degree q then {
						num := - coefficient(q, 0);
						den := leadingCoefficient q;
						yield fractionalRoot(num,den,n);
					}
				}
			}
		}
	}
}

