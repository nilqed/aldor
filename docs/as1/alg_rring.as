-------------------------- alg_rring.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2004
-- Copyright (c) INRIA 2004, Version 1.1.0
-- Logiciel libalgebra (c) INRIA 2004, dans sa version 1.1.0
-----------------------------------------------------------------------------

#include "algebra"


define RRing(R:Ring):Category == Join(Ring, Module R, LinearArithmeticType R);

