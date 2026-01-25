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
-------------------------- sit_intgmp.as ---------------------------------
-- Copyright (c) Helene Prieto 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it ©INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

extend GMPInteger: IntegerCategory == add {
	import {
		____gmpz__divexact: (%,%,%) -> ();
		____gmpz__gcdext: (%,%,%,%,%) -> ();
		____gmpz__tdiv__r: (%,%,%) -> ();
		____gmpz__tdiv__qr: (%,%,%,%) -> ();
	} from Foreign C;

#if DEBUG
	-- This assumes that Integer == AldorInteger
	integer(u:%):AldorInteger	== u::AldorInteger;
#else
	-- Those 2 assume that Integer == GmpInteger
	integer(u:%):Integer		== u;
	coerce(n:Integer):%		== n;
#endif

	remainder!(a:%, b:%):%		== { ____gmpz__tdiv__r(a, a, b); a }
	local NULL:%			== nil$Pointer pretend %;

	divide!(a:%, b:%, q:%):(%, %) == {
		r:% := new();
		____gmpz__tdiv__qr(q, r, a, b);
		(q, r);
	}

	quotient(x:%, y:%): % == {
		one? y => x;
		q:% := new();
		____gmpz__divexact(q,x,y);
		q;
	}

	extendedEuclidean(a:%, b:%): (%,%,%) == {
		import from MachineInteger;
		g:% := new();
		s:% := new();
		____gmpz__gcdext(g,s,NULL,a,b);
		s := remainder!(s, b);
		(g, s, quotient(g - a * s, b));
	}

	extendedEuclidean(a:%, b:%, c:%):Partial Cross(%, %) == {
		zero? c => [(0, 0)];
		import from Partial %;
		zero? b => {
			zero? a or failed?(u := exactQuotient(c, a)) => failed;
			[(retract u, 0)];
		}
		zero? a => {
			failed?(u := exactQuotient(c, b)) => failed;
			[(0, retract u)];
		}
		g:% := new();
		s:% := new();
		____gmpz__gcdext(g,s,NULL,a,b);
		failed?(u := exactQuotient(c, g)) => failed;
		s := remainder!(times!(s, retract u), b);
		[s, quotient(c - a * s, b)];
	}

	diophantine(a:%, b:%, m:%):Partial % == {
		assert(~zero? m);
		zero?(b := b rem m) => [0];
		zero?(a := a rem m) => failed;
		g:% := new();
		c:% := new();
		____gmpz__gcdext(g,c,NULL,a,m);
		failed?(u := exactQuotient(b, g)) => u;
		[remainder!(times!(c, retract u), m)];
	}

	-- TEMPORARY: THOSE 6 DEFAULTS ARE NOT TAKEN FROM IntegerCategory!!!
	canonicalUnitNormal?:Boolean	== true;
	karatsubaCutoff:MachineInteger	== 12;
	relativeSize(n:%):MachineInteger== { zero? n => 0; length n }
	unit?(x:%):Boolean		== one? x or x = -1;
	unitNormal(x:%):(%, %, %) == {
		import from MachineInteger;
		sign(x) < 0 => (-x,-1,-1);
		(x, 1, 1)
	};
	-- TEMPORARY: CANNOT OVERLOAD (BUG 1272)
	-- unitNormal(x:%, z:%):(%, %) == {
	unitNormalize(x:%, z:%):(%, %) == {
		import from MachineInteger;
		sign(x) < 0 => (-x,-z);
		(x, z)
	}
}

