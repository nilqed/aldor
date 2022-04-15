--------------------------- sit_linelim.as ----------------------------------
-- Copyright (c) Thom Mulders 1996
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1996
-----------------------------------------------------------------------------

#include "algebra"

macro {
	I == MachineInteger;
	ARR == PrimitiveArray;
}


define LinearEliminationCategory(R:CommutativeRing, M:MatrixCategory R):
	Category == with {
	if R has IntegralDomain then {
		denominators: (M,I->I,I,ARR I) -> ARR R;
		dependence: (Generator Vector R,I) -> (M,I -> I,I,R);
		deter: (M,I->I,I,I) -> R;
		determinant: M -> R;
		determinant!: M -> R;
	}
	extendedRowEchelon: M -> (M,I->I,I,ARR I,I,M);
	extendedRowEchelon!: M -> (I->I,I,ARR I,I,M);
	extendedRowEchelonForm: M -> (M,M);
	maxInvertibleSubmatrix: M -> (Array I, Array I);
	maxInvertibleSubmatrix!: M -> (Array I, Array I);
	pivot: (M, I -> I, I, I) -> I;
	if R has IntegralDomain then {
		rank: M -> I;
		rank!: M -> I;
	}
	rowEchelon: M -> (M,I->I,I,ARR I,I);
	rowEchelon!: M -> (I->I,I,ARR I,I);
	rowEchelon!: (M, M) -> (I->I,I,ARR I,I);
	rowEchelonForm: M -> M;
	span: M -> Array I;
	span!: M -> Array I;
	default {
		span(a:M):Array I == span! copy a;

		if R has IntegralDomain then {
			determinant(a:M):R	== determinant! copy a;
			rank(a:M):I		== rank! copy a;

			rank!(a:M):I == {
			-- TEMPORARY: BLOODY 1.1.12p4 COMPILER BUG OTHERWISE
				-- (p,r,st,d) := rowEchelon!(a);
				(p,r,st,d) := rowEchelon!(a,
						zero(numberOfRows a, 0$I));
				r;
			}

			determinant!(a:M):R == {
			-- TEMPORARY: BLOODY 1.1.12p4 COMPILER BUG OTHERWISE
				-- (p,r,st,d) := rowEchelon!(a);
				(p,r,st,d) := rowEchelon!(a,
						zero(numberOfRows a, 0$I));
				deter(a,p,r,d);
			}
		}

		span!(a:M):Array I == {
			import from I, ARR I;
			-- TEMPORARY: BLOODY 1.1.12p4 COMPILER BUG OTHERWISE
			-- (p,r,st,d) := rowEchelon!(a);
			(p,r,st,d) := rowEchelon!(a, zero(numberOfRows a, 0$I));
			[st i for i in 1..r];
		}

		maxInvertibleSubmatrix!(a:M):(Array I, Array I) == {
			import from I, ARR I;
			-- TEMPORARY: BLOODY 1.1.12p4 COMPILER BUG OTHERWISE
			-- (p,r,st,d) := rowEchelon!(a);
			(p,r,st,d) := rowEchelon!(a, zero(numberOfRows a, 0$I));
			([p i for i in 1..r], [st i for i in 1..r]);
		}

		maxInvertibleSubmatrix(a:M):(Array I, Array I) ==
			maxInvertibleSubmatrix! copy a;


		rowEchelon!(a:M):(I->I,I,ARR I,I) ==
			rowEchelon!(a, zero(numberOfRows a, 0));

		rowEchelon(a:M): (M,I->I,I,ARR I,I) == {
			copya := copy a;
			-- TEMPORARY: BLOODY 1.1.12p4 COMPILER BUG OTHERWISE
			-- (p,r,st,d) := rowEchelon!(copya);
			(p,r,st,d) :=
				rowEchelon!(copya,zero(numberOfRows copya,0$I));
			(copya,p,r,st,d);
		}

		rowEchelonForm(a:M):M == {
			import from I, ARR I;
			(b,p,r,st,d) := rowEchelon(a);
			(n, m) := dimensions b;
			c := zero(n,m);
			for i in 1..n repeat {
				for j in st(i)..m repeat c(i,j) := b(p(i),j);
			}
			c;
		}

		extendedRowEchelon(a:M): (M,I->I,I,ARR I,I,M) == {
			copya := copy a;
			(p,r,st,d,t) := extendedRowEchelon!(copya);
			(copya,p,r,st,d,t);
		}

		extendedRowEchelon!(a:M): (I->I,I,ARR I,I,M) == {
			b := one numberOfRows a;
			(p,r,st,d) := rowEchelon!(a, b);
			(p,r,st,d,b);
		}

		extendedRowEchelonForm(a:M): (M,M) == {
			import from I, ARR I;
			(b,p,r,st,d,t) := extendedRowEchelon(a);
			(n, m) := dimensions b;
			c := zero(n,m);
			u := zero(n,n);
			for i in 1..n repeat {
				for j in st(i)..m repeat c(i,j) := b(p(i),j);
				for j in 1..n repeat u(i,j) := t(p(i),j);
			}
			(c, u);
		}

		pivot(a:M, p:I->I, c:I, r:I):I == {
			import from Boolean, R;
			n := numberOfRows a;
			l := r;
			while (l <= n and zero? a(p l, c)) repeat l := next l;
			l > n => l;
			sz := relativeSize a(p l, c);
			for ll in next(l)..n repeat {
				if (~zero?(x := a(p ll, c))) and
					((s := relativeSize x) < sz) then {
						l := ll;
						sz := s;
				}
			}
			l;
		}
	}
}

