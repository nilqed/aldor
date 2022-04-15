---------------------------- alg_version.as ----------------------------------
--
-- This file provides utilities for storing version info in libraries
--
-- Copyright (c) Manuel Bronstein 2001
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "aldor"

macro {
	Z == MachineInteger;
	VER == "Algebra Library Version 1.1.0 - April 19, 2005";
	CPR1 == _
 "Algebra Library - Copyright (c) 1994-2005, ETH Zurich, INRIA and M.Bronstein";
	CPR2 == _
 "Algebra Library - Copyright (c) 1998-2007 Aldor Software Organization Ltd (Aldor.org), LIFL and M.Moreno Maza";
	CPRGMP == _
 "GMP version: must be linked with GMP (Free Software Foundation)";
}


AlgebraLibraryInformation: VersionInformationType == add {
	name:String	== "libalgebra";
	version:String	== VER;
	major:Z		== 1;
	minor:Z		== 1;
	patch:Z		== 0;

	credits:List String == {
		l := append!([CPR1, CPR2], credits$AldorLibraryInformation);
#if GMP
                l := append!(l, CPRGMP);
#endif
		l;
	}
}

