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
---------------------------- sal_gmptls.as -------------------------------
--
-- This file provides undocumented tools for GMP integer and float types
--
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro {
	Z == MachineInteger;
	BW == BinaryWriter;
	PZ == Record(z:Z);
}

GMPTools: with {
	readlimbs!: BinaryReader -> (Z, Pointer);
	writelimbs!: (BW, Z, Z, Generator Z) -> BW;
} == add {
	local wordsize:Z == bytes;

	writelimbs!(p:BW, sgn:Z, nlimbs:Z, limbs:Generator Z):BW == {
		import from Boolean, Z, Byte;
		p := p << sgn;				-- write sign first
		zero? sgn => p;
		p := p << nlimbs;			-- write size (limbs)
		for n in limbs repeat {
			nn := n;
			for m in 1..wordsize repeat {
				p := p << lowByte nn;
				nn := shift(nn, -8);
			}
		}
		p;
	}

	readlimbs!(p:BinaryReader):(Z, Pointer) == {
		import from Boolean, Byte, PZ;
		nlimbs:Z := << p;			-- read size first
		assert(nlimbs >= 0);
		p:PrimitiveArray Z := new nlimbs;
		byte := lowByte nlimbs;
		for i in 0..prev nlimbs repeat {
			n:Z := 0;
			st:Z := 0;
			for m in 1..wordsize repeat {
				byte := << p;
				n := n \/ shift(byte::Z, st);
				st := st + 8;
			}
			p.i := n;
		}
		(nlimbs, pointer p);
	}
}
