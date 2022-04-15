#include "algebra"

macro {
	SingleInteger == MachineInteger;
	CRT == ChineseRemaindering %;
}

ModularComputation: Category == CanonicalSimplification with {
        residueClassRing: (p: %) -> ResidueClassRing(%,p);
	if % has EuclideanDomain then {
            combine: (%, %) -> (%, %) -> %;
            ++ `combine(M1,M2)(a,b)' returns `c' such that `c mod M1'
            ++ is `a', `c mod M2' is `b' and `c mod (M1*M2)' is `c'.
            ++ This assumes that `M1' and `M2' are relatively prime.
	    if % has IntegerType then {
	        combine: (%, SingleInteger) -> (%, SingleInteger) -> %;
        	++`combine(M,m)(a,i)' returns the same `combine(M,m::%)(a,i::%)'
	    }
	}
	default {
	    if % has EuclideanDomain then {
		combine(M1: %, M2: %): (%, %) -> % == combine(M1, M2)$CRT;
		if % has IntegerType then {
		    combine(M:%, m:SingleInteger):(%, SingleInteger) -> % == {
			    combine(M, m)$CRT;
		    }
		}
	    }
	}
}

