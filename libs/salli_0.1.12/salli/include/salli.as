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
----------------------- salli.as -------------------------
--
-- Header file for salli clients
--
-- Used compile-time symbols:
--    AGAT:      agat on when asserted     AGAT(stream, value);
--    TIME:      profile on when asserted  TIMESTART; ...; TIME(message);
--    TRACE:     trace on when asserted    TRACE(message, value);
--
-- Copyright (c) Manuel Bronstein 1998-2000
-- Copyright (c) INRIA 2000, Version 0.1.12f
-- Logiciel Salli ©INRIA 2000, dans sa version 0.1.12f
-----------------------------------------------------------------------------

#unassert ALDOC
#unassert SALLITEST

macro {
	rep x == ((x)@%) pretend Rep;
	per r == ((r)@Rep) pretend %;
}

#library salli "libsalli.al"
import from salli;
inline from salli;

#if DontImportFromBoolean
#else
import from Boolean;
#endif

-- Macros for simple profiling
#if TIME
macro {
	TIMESTART	== { import from Character, String, MachineInteger, _
				Timer, TextWriter; _
				start!(SaLlIcLoCk := timer()); }
	TIME(msg)	== { stderr<<msg<<space<<read SaLlIcLoCk<<newline; }
}
#else
macro {
	TIMESTART	== {};
	TIME(msg)	== {};
}
#endif

-- Macros for simple tracing
#if TRACE
macro TRACE(str, val) == { import from WriterManipulator, TextWriter, String;_
				stderr << str << val << endnl; }
#else
macro TRACE(str, val) == {};
#endif

-- Macros for Agat animation
#if AGAT
macro AGAT(str, val) == { import from Agat; agat(str, val); }
#else
macro AGAT(str, val) == {};
#endif

