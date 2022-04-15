---------------------------- sit_prfcat.as --------------------------------
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"


macro {
	Z == Integer;
	FR == FractionalRoot;
	RR == FractionalRoot Z;
	POLY == UnivariatePolynomialAlgebra0;
}

define PrimeFieldCategory:Category ==
	Join(PrimeFieldCategory0, FactorizationRing) with{
		rootsSqfr: (P:POLY %) -> P -> Generator %;
	default {
		rationalRoots(P:POLY %):P -> Generator RR == integerRoots P;

		local ratroot(r:FR %):RR ==
			integralRoot(lift integralValue r, multiplicity r);

		roots(P:POLY %):P -> Generator FR % == {
			import from Boolean,PrimeFieldUnivariateFactorizer(%,P);
			(p:P):Generator FR % +-> roots(p, false);
		}

		rootsSqfr(P:POLY %):P -> Generator % == {
			import from Boolean, FR %;
			import from PrimeFieldUnivariateFactorizer(%, P);
			(p:P):Generator % +-> generate {
				for r in roots(p, true) repeat
					yield integralValue r;
			}
		}

		integerRoots(P:POLY %):P -> Generator RR == {
			rootP := roots P;
			(p:P):Generator RR +-> generate {
				for r in rootP p repeat yield ratroot r;
			}
		}

		factor(P:POLY %):P -> (%, Product P) == {
			import from PrimeFieldUnivariateFactorizer(%, P);
			(p:P):(%, Product P) +-> factor p;
		}
	}
}
