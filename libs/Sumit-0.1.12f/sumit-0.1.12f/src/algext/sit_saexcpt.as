-- ======================================================================
-- This code was written all or part by Dr. Manuel Bronstein from
-- Inria-CAFE project team. After his sudden death on June 6, 2005, Inria
-- decided to publish this code under the CeCILL open source license in
-- memory of Dr. Manuel Bronstein.
-- 
-- This software is governed by the CeCILL license under French law and
-- abiding by the rules of distribution of free software. You can use,
-- modify and/or redistribute the software under the terms of the CeCILL
-- license as circulated by CEA, CNRS and Inria at the following URL :
-- http://www.cecill.info/licences/Licence_CeCILL_V2-en.html
-- 
-- As a counterpart to the access to the source code and rights to copy,
-- modify and redistribute granted by the license, users are provided
-- only with a limited warranty and the software's author, the holder of
-- the economic rights, and the successive licensors have only limited
-- liability.
-- 
-- In this respect, the user's attention is drawn to the risks associated
-- with loading, using, modifying and/or developing or reproducing the
-- software by the user in light of its specific status of free software,
-- that may mean that it is complicated to manipulate, and that also
-- therefore means that it is reserved for developers and experienced
-- professionals having in-depth computer knowledge. Users are therefore
-- encouraged to load and test the software's suitability as regards
-- their requirements in conditions enabling the security of their
-- systems and/or data to be ensured and, more generally, to use and
-- operate it in the same conditions as regards security.
-- 
-- The fact that you are presently reading this means that you have had
-- knowledge of the CeCILL license and that you accept its terms.
-- ======================================================================
-- 
----------------------------- sit_saexcpt.as --------------------------------
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{ReducibleModulusException}
\History{Manuel Bronstein}{15/11/99}{created}
\Usage{
throw \this(R, m, a)\\
try \dots catch E in
\{ E has \astype{ReducibleModulusExceptionType} R => \dots \}
}
\Params{
{\em R} & \astype{CommutativeRing} & A commutative ring\\
{\em m} & R & The modulus\\
{\em a} & R & A proper factor of $m$\\
}
\Descr{\this(R, m, a) is an exception type thrown by inversion modulo
a reducible element of R.}
#endif
ReducibleModulusException(R:CommutativeRing, m:R, a:R):
	ReducibleModulusExceptionType R == add {
		modulus:R == m;
		factor:R == a;
}

#if ALDOC
\thistype{ReducibleModulusExceptionType}
\History{Manuel Bronstein}{15/11/99}{created}
\Usage{\this~R: Category}
\Params{ {\em R} & \astype{CommutativeRing} & A commutative ring\\ }
\Descr{\this~R~is the category of exceptions thrown by inversion modulo
a reducible element of R. The constants {\tt modulus} and {\tt factor}
contain the modulus and a proper factor respectively.}
#endif
define ReducibleModulusExceptionType(R:CommutativeRing):Category == with {
	modulus: R;
	factor: R;
}

