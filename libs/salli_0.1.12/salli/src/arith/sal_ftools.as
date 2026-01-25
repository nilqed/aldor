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
---------------------------- sal_ftools.as -------------------------------
--
-- This file provides undocumented tools for float-like types
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro Z == MachineInteger;

-- internal type giving common implementations to concrete FloatType's
FloatTypeTools(T:FloatType): with {
	print: (T, Z, Z, TextWriter) -> TextWriter;
} == add {
	local ten:T		== { import from Z; 10::T; }
	local plus:Character	== { import from Z; char  43; }
	local minus:Character	== { import from Z; char  45; }
	local dot:Character	== { import from Z; char  46; }
	local e:Character	== { import from Z; char 101; }

	-- prints x 10^k showing at most n digits after the decimal point
	print(x:T, k:Z, n:Z, p:TextWriter):TextWriter == {
		import from AldorInteger, Boolean, Character;
		assert(x >= 1); assert(x < 10.0);
		p := p << truncate x;
		zero?(x := fraction x) => print(k, p);
		p := p << dot;
		i:Z := 0;
		while i < n and ~zero?(x) repeat {
			x := ten * x;
			p := p << char machine(48 + truncate x);
			x := fraction x;
			i := next i;
		}
		print(k, p);
	}

	local print(k:Z, p:TextWriter):TextWriter == {
		zero? k => p;
		p := p << e;
		if k > 0 then p := p << plus;
		p << k;
	}
}

