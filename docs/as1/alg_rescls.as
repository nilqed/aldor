#include "algebra"

+++ A domain of `ResidueClassRing(R,p)' implements a commutative
+++ ring isomorphic with `R/p'

define ResidueClassRing(R: CommutativeRing, p: R): Category == CommutativeRing with {
        modularRep: R -> %;
	++ `modularRep(r)' returns the residue class of `r'
        canonicalPreImage: % -> R;
	++ `canonicalPreImage(x)' returns `r' such that
	++ `modularRep(r)' returns `x' and `unitNormal(r) = (u, r, v)'
	++ where u, v belong to `R'
        if R has EuclideanDomain then {
		symmetricPreImage: % -> R;
		++ see Kaltofen Monagan ISSAC 1999
		if R has SourceOfPrimes then {
			if prime?(p)$R then {
				Field;
			}
				
		}

        }
	
}

