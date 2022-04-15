----------------------------- sit_fftring.as --------------------------------
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"


define FFTRing: Category == CommutativeRing with {
	fft: (P: UnivariatePolynomialAlgebra0 %) -> (P, P) -> Partial P;
	fft!: (P: UnivariatePolynomialAlgebra0 %) -> (P, P, P) -> Boolean;
	fftCutoff: MachineInteger;
}

