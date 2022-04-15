------------------------   sit_laring.as   -----------------------
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"

macro {
	B == Boolean;
	I == MachineInteger;
	V == Vector;
	A == Array;
	ARR == PrimitiveArray;
}


define LinearAlgebraRing: Category == IntegralDomain with {
	determinant: (M:MatrixCategory %) -> M -> %;
	factorOfDeterminant: (M:MatrixCategory %) -> M -> (B, %);
	inverse: (M:MatrixCategory %) -> M -> (M, V %);
	invertibleSubmatrix: (M:MatrixCategory %) -> M -> (B, A I, A I);
	kernel: (M:MatrixCategory %) -> M -> M;
	linearDependence: (Generator V %, I) -> V %;
	maxInvertibleSubmatrix: (M:MatrixCategory %) -> M -> (A I, A I);
	particularSolution: (M:MatrixCategory %) -> (M, M) -> (M, V %);
	rank: (M:MatrixCategory %) -> M -> I;
	rankLowerBound: (M:MatrixCategory %) -> M -> (B, I);
	solve: (M:MatrixCategory %) -> (M, M) -> (M, M, V %);
	span: (M:MatrixCategory %) -> M -> A I;
	subKernel: (M:MatrixCategory %) -> M -> (B, M);
	default {
		factorOfDeterminant(M:MatrixCategory %):M -> (B, %) == {
			(m:M):(B, %) +-> (true, determinant(M)(m));
		}

		rankLowerBound(M:MatrixCategory %):M -> (B, I) == {
			(m:M):(B, I) +-> (true, rank(M)(m));
		}

		invertibleSubmatrix(M:MatrixCategory %):M -> (B, A I, A I) == {
			(m:M):(B, A I, A I) +-> {
				(r, c) := maxInvertibleSubmatrix(M)(m);
				(true, r, c);
			}
		}

		subKernel(M:MatrixCategory %):M -> (B, M) == {
			(m:M):(B, M) +-> (true, kernel(M)(m));
		}
	}
}
