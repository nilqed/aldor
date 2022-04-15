------------------------   sit_linalg.as   -----------------------
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"
#include "aldorio"

macro {
	B == Boolean;
	I == MachineInteger;
	V == Vector;
	A == Array;
	ARR == PrimitiveArray;
}


LinearAlgebra(R:CommutativeRing, M:MatrixCategory R): with {
	if R has IntegralDomain then {
		cycle: (M, V R) -> (V R, M);
		cycle: (V R -> V R, V R) -> (V R, M);
		determinant: M -> R;
		factorOfDeterminant: M -> (B, R);
		firstDependence: (Generator V R, I) -> V R;
		inverse: M -> (M, V R);
	}
	invertibleSubmatrix: M -> (B, A I, A I);	-- rows/cols
	if R has IntegralDomain then {
		kernel: M -> M;
	}
	maxInvertibleSubmatrix: M -> (A I, A I);	-- rows/cols
	if R has IntegralDomain then {
		particularSolution: (M, M) -> (M, V R);
		rank: M -> I;
		rankLowerBound: M -> (B, I);
	}
	span: M -> A I;
	if R has IntegralDomain then {
		solve: (M, M) -> (M, M, V R);
		subKernel: M -> (B, M);
	}
} == add {
	local gcd?:Boolean	== R has GcdDomain;
	local laring?:Boolean	== R has LinearAlgebraRing;
	local special?:Boolean	== R has Specializable;

	local elim:LinearEliminationCategory(R, M) == {
		R has Field => OrdinaryGaussElimination(R, M);
		R has IntegralDomain =>
			TwoStepFractionFreeGaussElimination(R, M);
		DivisionFreeGaussElimination(R, M);
	}

	span(m:M):A I == {
		laring? => laspan m;
		span(m)$elim;
	}

	maxInvertibleSubmatrix(m:M):(A I,A I) == {
		laring? => lamaxinv m;
		maxInvertibleSubmatrix(m)$elim;
	}

	invertibleSubmatrix(m:M):(B, A I, A I) == {
		laring? => lasubinv m;
		(r, c) := maxInvertibleSubmatrix m;
		(true, r, c);
	}

	if R has IntegralDomain then {

		cycle(a:M, v:V R):(V R, M) == cycle((w:V R):V R +-> a * w, v);

		determinant(m:M):R == {
			laring? => ladet m;
			determinant(m)$elim;
		}

		rank(m:M):I == {
			laring? => larank m;
			rank(m)$elim;
		}

		subKernel(m:M):(B, M) == {
			laring? => lasubker m;
			(true, kernel m);
		}

		inverse(m:M):(M, V R) == {
			laring? => lainv m;
			inverse! copy m;
		}

		factorOfDeterminant(m:M):(B, R) == {
			laring? => lafactdet m;
			(true, determinant m);
		}

		rankLowerBound(m:M):(B, I) == {
			import from Partial Cross(B, I);
			laring? => lalbrank m;
			special? => {
				failed?(u := speclbrank m) => (true, rank m);
				retract u;
			}
			(true, rank m);
		}

		solve(a:M, b:M):(M, M, V R) == {
			import from I;
			(ra, ca) := dimensions a;
			(rb, cb) := dimensions b;
			ra ~= rb => {
			    error("Number of rows must match");
			}
			assert(ra = rb);
			if zero? ra then { a := zero(1, ca); b := zero(1, cb) }
			laring? => lasolve(a, b);
			gcd? => solvegcddomain!(copy a, copy b);
			solvegeneral!(copy a, copy b);
		}

		particularSolution(a:M, b:M):(M, V R) == {
			laring? => lapsol(a, b);
			psol!(copy a, copy b);
		}

		kernel(m:M):M == {
			import from I, OverdeterminedLinearSystemSolver(R, M);
			(r, c) := dimensions m;
			zero? c => zero(0, 0);
			if zero? r then m := zero(1, c);
			laring? => kernel!(m, lakernel);
			kernel!(copy m, nullspace!);
		}

		cycle(f:V R -> V R, v:V R):(V R, M) == {
			import from I;
			n := #v;
			m := zero(n, next n);
			dep := firstDependence(cycle(f, v, m), #v);
			(dep, m);
		}

		-- stores each vector generated as a column of m
		local cycle(f:V R -> V R, v:V R, m:M):Generator V R == {
			generate {
				j:I := 1;
				n := numberOfRows m;
				vv := copy v;
				for i in 1..n repeat m(i,j) := vv.i;
				yield vv;
				repeat {
					vv := f vv;
					j := next j;
					for i in 1..n repeat m(i,j) := vv.i;
					yield vv;
				}
			}
		}

		local first(w:V R, n:I):V R == {
			assert(n <= #w);
			n = #w => w;
			v := zero n;
			for i in 1..n repeat v.i := w.i;
			v;
		}

		firstDependence(gen:Generator V R, n:I):V R == {
			import from ARR I;
			laring? => ladep(gen, n);
			(a,p,r,d) := dependence(gen, n)$elim;
			st:ARR I:= new r;	-- ignore st(0)
			for i in 1..prev r repeat st(i) := i;
			gcd? => first(gcddep(a,p,st,prev r,r), r);
			first(generaldep(a,p,st,prev r,r,d), r);
		}

		local psol!(a:M, b:M):(M, V R) == {
			gcd? => psolgcddomain!(a, b);
			psolgeneral!(a, b);
		}

		local inverse!(a:M):(M, V R) == {
			assert(square? a);
			gcd? => invgcddomain! a;
			invgeneral! a;
		}

		local nullspace!(a:M):M == {
			-- TEMPORARY: BLOODY 1.1.12p4 COMPILER BUG OTHERWISE
			-- (p,r,st,d) := rowEchelon!(a)$elim;
			(p,r,st,d) :=
				rowEchelon!(a, zero(numberOfRows a, 0$I))$elim;
			gcd? => nullgcddomain!(a, p, r, st);
			nullgeneral!(a, p, r, st);
		}

		local generaldep(a:M, p:I->I, st:ARR I, c:I, r:I, d:R):V R == {
			import from Backsolve(R, M);
			backsolve(a,p,st,c,r,d);
		}

		local invgeneral!(a:M):(M, V R) == {
			import from Backsolve(R, M);
			(p,r,st,d,w) := extendedRowEchelon!(a)$elim;
			det := deter(a,p,r,d)$elim;
			backsolve(a,p,st,r,w,det);
		}

		local nullgeneral!(a:M, p:I->I, r:I, st:ARR I):M == {
			import from ARR R, Backsolve(R, M);
			zero? r => one numberOfColumns a;
			den := denominators(a,p,r,st)$elim;
			k:List V R := empty;
			(n, m) := dimensions a;
			un:R := 1;
			for j in 1..st(1)-1 repeat
				k := cons(backsolve(a,p,st,0,j,un),k);
			for i in 1..prev r repeat
				for j in next(st i)..prev st(next i) repeat
					k:=cons(backsolve(a,p,st,i,j,den(i)),k);
			if r > 0 then
				for j in next(st r)..m repeat
					k:=cons(backsolve(a,p,st,r,j,den(r)),k);
			[v for v in k];
		}

		local solvegeneral!(a:M, b:M):(M, M, V R) == {
			import from Backsolve(R, M);
			(p,r,st,d) := rowEchelon!(a, b)$elim;
			det := deter(a,p,r,d)$elim;
			(psol, den) := backsolve(a,p,st,r,b,det);
			(nullgeneral!(a, p, r, st), psol, den);
		}

		local psolgeneral!(a:M, b:M):(M, V R) == {
			import from Backsolve(R, M);
			(p,r,st,d) := rowEchelon!(a, b)$elim;
			det := deter(a,p,r,d)$elim;
			backsolve(a,p,st,r,b,det);
		}
	}

	if R has GcdDomain then {

		local gcddep(a:M, p:I->I, st:ARR I, c:I, r:I):V R == {
			import from Backsolve(R, M);
			backsolve(a,p,st,c,r);
		}

		local invgcddomain!(a:M):(M, V R) == {
			import from Backsolve(R, M);
			(p,r,st,d,w) := extendedRowEchelon!(a)$elim;
			backsolve(a,p,st,r,w);
		}

		local nullgcddomain!(a:M, p:I->I, r:I, st:ARR I):M == {
			import from Backsolve(R, M);
			zero? r => one numberOfColumns a;
			k:List V R := empty;
			(n, m) := dimensions a;
			for j in 1..prev(st 1) repeat
				k := cons(backsolve(a,p,st,0,j),k);
			for i in 1..prev r repeat
				for j in next(st i)..prev st(next i) repeat
					k:=cons(backsolve(a,p,st,i,j),k);
			if r > 0 then for j in next(st r)..m repeat
					k:=cons(backsolve(a,p,st,r,j),k);
			[v for v in k];
		}

		local solvegcddomain!(a:M, b:M):(M, M, V R) == {
			import from Backsolve(R, M);
			(p,r,st,d) := rowEchelon!(a, b)$elim;
			(psol, den) := backsolve(a,p,st,r,b);
			(nullgcddomain!(a, p, r, st), psol, den);
		}

		local psolgcddomain!(a:M, b:M):(M, V R) == {
			import from Backsolve(R, M);
			(p,r,st,d) := rowEchelon!(a, b)$elim;
			backsolve(a,p,st,r,b);
		}
	}

	if R has Specializable then {
		speclbrank(m:M):Partial Cross(B, I) ==
			rankLowerBound(m)$SpecializationLinearAlgebra(R, M);
	}

	if R has LinearAlgebraRing then {
		local ladet(a:M):R == {
			import from R;
			determinant(M)(a);
		}

		local larank(a:M):I == {
			import from R;
			rank(M)(a);
		}

		local laspan(a:M):A I == {
			import from R;
			span(M)(a);
		}

		local lamaxinv(a:M):(A I, A I) == {
			import from R;
			maxInvertibleSubmatrix(M)(a);
		}

		local lafactdet(a:M):(B, R) == {
			import from R;
			factorOfDeterminant(M)(a);
		}

		local lalbrank(a:M):(B, I) == {
			import from R;
			rankLowerBound(M)(a);
		}

		local lasubinv(a:M):(B, A I, A I) == {
			import from R;
			invertibleSubmatrix(M)(a);
		}

		local lasubker(a:M):(B, M) == {
			import from R;
			subKernel(M)(a);
		}

		local lainv(a:M):(M, V R) == {
			import from R;
			inverse(M)(a);
		}

		local lasolve(a:M, b:M):(M, M, V R) == {
			import from R;
			solve(M)(a, b);
		}

		local lapsol(a:M, b:M):(M, V R) == {
			import from R;
			particularSolution(M)(a, b);
		}

		local lakernel(a:M):M == {
			import from R;
			kernel(M)(a);
		}

		local ladep(gen:Generator V R, n:I):V R == {
			import from R;
			linearDependence(gen, n);
		}
	}
}
