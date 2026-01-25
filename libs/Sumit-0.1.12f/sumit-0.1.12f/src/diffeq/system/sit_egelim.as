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
------------------------------ sit_egelim.as ------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	B == Boolean;
	I == MachineInteger;
	Z == Integer;
	A == Array;
}

LinearOrdinaryRecurrenceEGElimination(R:IntegralDomain,
		RX: UnivariatePolynomialCategory R,
		M: MatrixCategory RX): with {
			trailingIndicialEquation: (A M, I) -> RX;
} == add {
	local zeroRow?(mat:M, n:I, i:I):Boolean == {
		import from RX;
		for j in 1..n repeat {
			~zero?(mat(i, j)) => return false;
		}
		true;
	}

	-- returns the number of leading zero rows at row r
	local leadingZeroRows(a:A M, n:I, r:I):I == {
		z:I := 0;
		d := #a;
		for i in 1..d while zeroRow?(a(d-i), n, r) repeat z := next z;
		z;
	}

	--returns the array of leading zero rows at all rows 
	local leadingWidths(a:A M, n:I): A I == {
		import from A I;
		w: A I := new n;
		for i in 0..n-1 repeat w.i := leadingZeroRows(a, n, i+1);
		w;
	}

	-- returns the number of trailing zero rows at row r
	local trailingZeroRows(a:A M, n:I, r:I):I == {
		z:I := 0;
		for mat in a while zeroRow?(mat, n, r) repeat z := next z;
		z;
	}   

	-- returns a list of pairs (i, ni) where i = row number
	-- and ni > 0 is the number of trailing zero rows at row i
	local trailingZeroRows(a:A M, n:I):List Cross(I, I) == {
		l:List Cross(I, I) := empty;
		for i in 1..n repeat {
			d := trailingZeroRows(a, n, i);
			if d > 0 then l := cons((i, d), l);
		}
		l;
	}

	-- returns the index of the row with the smallest # of leading zero rows
	-- among the ones such that v.i is not 0
	local minLeadingZeroRow(a:A M, n:I, v:Vector RX):I == {
		import from Boolean, RX;
		assert(~zero? v);
		index:I := 1;
		while zero?(v.index) repeat index := next index;
		leading := leadingZeroRows(a, n, index);
		for i in next(index)..n | ~zero?(v.i) repeat {
			d := leadingZeroRows(a, n, i);
			if d < leading then {
				index := i;
				leading := d;
			}
		}
		index;
	}

	local deepCopy(a:A M, n:I):A M == {
		import from M;
		b:A M := new(d := #a);
		for i in 0..prev d repeat b.i := copy(a.i);
		b;
	}

	trailingIndicialEquation(a:A M, n:I):RX ==
		trailingIndicialEquation!(deepCopy(a, n), n);

	local trailingIndicialEquation!(a:A M, n:I):RX == {
		while zero?(eq := egelim!(a, n)) repeat {};
		TRACE("egelim::trailingIndicialEquation!: eq = ", eq);
		eq;
	}

	local egelim!(a:A M, n:I):RX == {
		import from Boolean, List Cross(I, I), Vector RX, M;
		import from LinearAlgebra(RX, M);
		import from A I;
		TIMESTART;
		TRACE("egelim::egelim!: a.0 = ", a.0);
		zRow? := false;
		for pair in trailingZeroRows(a, n) repeat {
			(i, ni) := pair;
			if shift!(a, n, i, ni) then zRow? := true;
		}
		TIME("egelim::egelim!: shifted a.0 at ");
		TRACE("egelim::egelim!: shifted a.0 = ", a.0);
		zRow? => {	-- TEMPORARY (MUST HANDLE THIS EVENTUALLY)
			import from String;
			error "egelim: got a full zero row";
		}
		(rank?, rk) := rankLowerBound(a.0);
		TIME("egelim::egelim!: rank at ");
		rk = n => determinant(a.0);
		ker := kernel transpose(a.0);
		TIME("egelim::egelim!: kernel at ");
		zero?(nc := numberOfColumns ker) => determinant(a.0);
		TRACE("egelim::egelim!: ker = ", ker);
                widths := leadingWidths(a, n);
                ls := makeConformed(ker, widths, n, nc);
		TIME("egelim::egelim!: conformed at ");
		for c in 1..nc repeat {
	       		v := column(ker, c);
			i := ls(c-1);
			for mat in a repeat {
				w := transpose(mat) * v;
				for j in 1..n repeat mat(i, j) := w.j;
			}
		}
		-- old code: 1-shot per kernel
		-- v := column(ker, 1);
		-- i := minLeadingZeroRow(a, n, v);
		-- for mat in a repeat {
			-- w := transpose(mat) * v;
			-- for j in 1..n repeat mat(i, j) := w.j;
		-- }
		TIME("egelim::egelim!: done at ");
		0;
	}

	-- return true if row s = #a, which means that row r is all 0
	local shift!(a:A M, n:I, r:I, s:I):Boolean == {
		import from Z, R, RX, M;
		assert(s > 0); assert(s <= #a);
		sr := s::Z::R;
		(d := prev(#a)) <= s => true;
		for i in s..d repeat {
			source := a.i;
			target := a(i - s);
			for j in 1..n repeat
				target(r, j) := translate(source(r, j), sr);
		}
		for i in d-s+1..d repeat {
			mat := a.i;
			for j in 1..n repeat mat(r, j) := 0;
		}
		false;
	}

	-- returns pair of matrix conformed to widths given and corresponding ordering   
	local makeConformed(ker: M, w: A I, n: I, nc: I): A I == {
		import from RX;
		ls: A I := new nc;
		for c in 1..nc repeat {
			l:I := 0;
			currentW:I := -1;
			for i in 1..n | ker(i, c)~=0 repeat if w(i-1)>currentW then {
				l := i;
				currentW := w(i-1);
                	}
			ls(c-1) := l;
			el := ker(l, c);
			for j in (c+1)..nc | ker(l,j)~=0 repeat {
				ej := ker (l, j);
				for i in 1..n repeat 
					ker(i, j) := ker(i,j)*el-ker(i,c)*ej;
			}
		}	
		ls;	
	} 
}
