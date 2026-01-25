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
--------------------------- sit_sprfmat.as ------------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it ©INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	Z == MachineInteger;
	A == PrimitiveArray Z;
	M == PrimitiveArray A;
	V == Vector F;
}

-- Do not use the log table for small prime, since the lazy strategy is better
SmallPrimeFieldCategoryLinearAlgebra(F:SmallPrimeFieldCategory0,
					MF:MatrixCategory F): with {
	determinant: MF -> F;
	inverse: MF -> (MF, V);
	kernel: MF -> MF;
	linearDependence: (Generator V, Z) -> V;
	maxInvertibleSubmatrix: MF -> (Array Z, Array Z);
	particularSolution: (MF, MF) -> (MF, V);
	rank: MF -> Z;
	solve: (MF, MF) -> (MF, MF, V);
	span: MF -> Array Z;
} == add {
	local charac:Integer	== characteristic$F;
	-- TEMPORARY: TERRIBLE 1.1.11e/12 COMPILER BUG (1181?)
	-- local schar:Z	== machine charac;

	local array(m:MF, r:Z, c:Z):M == {
		import from A, F;
		a := array(r, c);
		c1 := prev c;
		for i in 0..prev r repeat for j in 0..c1 repeat
			a.i.j := machine m(next i, next j);
		a;
	}

	local array(r:Z, c:Z):M == {
		import from A;
		a:M := new r;
		for i in 0..prev r repeat a.i := new c;
		a;
	}

	local matrix(a:M, r:Z, c:Z):MF == {
		import from A, F;
		m:MF := zero(r, c);
		for i in 1..r repeat for j in 1..c repeat
			m(i, j) := a(prev i)(prev j)::F;
		m;
	}

	local vector(a:A, n:Z):V == {
		import from F;
		v:V := zero n;
		for i in 1..n repeat v.i := a(prev i)::F;
		v;
	}

	local genp(g:Generator V, n:Z, a:A):Generator A == generate {
		import from F, V;
		for v in g repeat {
			assert(n = #v);
			for i in 1..n repeat a(prev i) := machine(v.i);
			yield a;
		}
	}

	linearDependence(g:Generator V, n:Z):V == {
		import from A, M, F, ModulopGaussElimination;
		-- TEMPORARY: TERRIBLE 1.1.11e/12 COMPILER BUG (1181?)
		schar := machine charac;
		a:A := new n;
		work := array(n, n1 := next n);
		ans := array(n1, 1);
		r := firstDependence!(genp(g, n, a), n, schar, work, ans);
		assert(r <= n1);
		v:V := zero r;
		for i in 1..r repeat v.i := ans(prev i)(0)::F;
		v;
	}

	determinant(m:MF):F == {
		import from Z, ModulopGaussElimination;
		assert(square? m);
		n := numberOfRows m;
		a := array(m, n, n);
		-- TEMPORARY: TERRIBLE 1.1.11e/12 COMPILER BUG (1181?)
		schar := machine charac;
		determinant!(a, n, schar)::F;
	}

	inverse(m:MF):(MF, V) == {
		import from Z, A, ModulopGaussElimination;
		assert(square? m);
		n := numberOfRows m;
		a := array(m, n, n);
		b := array(n, n);
		d:A := new n;
		-- TEMPORARY: TERRIBLE 1.1.11e/12 COMPILER BUG (1181?)
		schar := machine charac;
		inverse!(a, n, schar, b, d);
		(matrix(b, n, n), vector(d, n));
	}

	kernel(m:MF):MF == {
		import from Z, ModulopGaussElimination;
		(r, c) := dimensions m;
		a := array(m, r, c);
		b := array(c, c);
		-- TEMPORARY: TERRIBLE 1.1.11e/12 COMPILER BUG (1181?)
		schar := machine charac;
		k := kernel!(a, r, c, schar, b);
		matrix(b, c, k);
	}

	maxInvertibleSubmatrix(m:MF):(Array Z, Array Z) == {
		import from Z, ModulopGaussElimination;
		(r, c) := dimensions m;
		a := array(m, r, c);
		-- TEMPORARY: TERRIBLE 1.1.11e/12 COMPILER BUG (1181?)
		schar := machine charac;
		maxInvertibleSubmatrix!(a, r, c, schar);
	}

	particularSolution(m:MF, q:MF):(MF, V) == {
		import from Z, A, ModulopGaussElimination;
		(r, c) := dimensions m;
		a := array(m, r, c);
		assert(r = numberOfRows q);
		cq := numberOfColumns q;
		b := array(q, r, cq);
		w := array(c, cq);
		d:A := new cq;
		-- TEMPORARY: TERRIBLE 1.1.11e/12 COMPILER BUG (1181?)
		schar := machine charac;
		particularSolution!(a, r, c, b, cq, schar, w, d);
		(matrix(w, c, cq), vector(d, cq));
	}

	rank(m:MF):Z == {
		import from Z, ModulopGaussElimination;
		(r, c) := dimensions m;
		a := array(m, r, c);
		-- TEMPORARY: TERRIBLE 1.1.11e/12 COMPILER BUG (1181?)
		schar := machine charac;
		rank!(a, r, c, schar);
	}

	span(m:MF):Array Z == {
		import from Z, ModulopGaussElimination;
		(r, c) := dimensions m;
		a := array(m, r, c);
		-- TEMPORARY: TERRIBLE 1.1.11e/12 COMPILER BUG (1181?)
		schar := machine charac;
		span!(a, r, c, schar);
	}

	solve(m:MF, q:MF):(MF, MF, V) == {
		import from Z, A, ModulopGaussElimination;
		(r, c) := dimensions m;
		a := array(m, r, c);
		kern := array(c, c);
		assert(r = numberOfRows q);
		cq := numberOfColumns q;
		b := array(q, r, cq);
		w := array(c, cq);
		d:A := new cq;
		-- TEMPORARY: TERRIBLE 1.1.11e/12 COMPILER BUG (1181?)
		schar := machine charac;
		k := solve!(a, r, c, b, cq, schar, w, d, kern);
		(matrix(kern, c, k), matrix(w, c, cq), vector(d, cq));
	}
}
