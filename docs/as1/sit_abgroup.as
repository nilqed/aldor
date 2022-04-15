------------------------------ sit_abgroup.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"


define AbelianGroup: Category == Join(AdditiveType, AbelianMonoid);

