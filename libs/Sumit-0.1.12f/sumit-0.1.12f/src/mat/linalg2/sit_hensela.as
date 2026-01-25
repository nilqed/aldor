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
---------------------------- sit_hensela.as ------------------------------------
-- Copyright (c) Helene Prieto 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it ©INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I == MachineInteger;
	V == Vector FX;
	Fx == Fraction FX;
	VU == Vector Fx;
}

UnivariatePolynomialHenselLinearAlgebra(F:Field,
		FX:UnivariatePolynomialCategory F,
		M:MatrixCategory FX): with {
	determinant: M -> Partial FX;
	particularSolution: (M, V) -> Partial VU;
} == add {
	local divideByX(p:FX):FX	== { import from Integer; shift(p,-1); }
	local multiplyByX(p:FX):FX	== { import from Integer; shift(p, 1); }
	local multiplyByX!(p:FX):FX	== { import from Integer; shift!(p,1); }
	local val0(p:FX):F	== { import from Integer; coefficient(p,0); }

	determinant(A:M):Partial FX == {
		import from I, Integer, FX, Fx, Partial VU;
		import from VectorOverFraction(FX, Fx);
		import from UnivariatePolynomialCRTLinearAlgebra(F, FX, M);
		n := numberOfRows A;
		assert(n = numberOfColumns A); assert(n > 0);
		b:V := zero n;
		for i in 1..n repeat b.i := random 1;	-- try linear rhs
		b.n := 1;				-- make sure b <> 0
		failed?(u := particularSolution(A, b)) => failed;
		y := retract u;
		(d, ignore) := makeIntegral y;
		determinant(A, d);
	}

	particularSolution(A:M, b:V):Partial VU == {
		import from I, Integer, F, FX, Fx, Partial Fx;
		TRACE("hensela::particularSolution: A = ", A);
		TRACE("hensela::particularSolution: b = ", b);
		(n, m) := dimensions A;
		(sol?, s, k, l, N, D, w, Q) := padicSolution(A, b, n, m);
		TRACE("hensela::particularSolution: s = ", s);
		TRACE("hensela::particularSolution: k = ", k);
		TRACE("hensela::particularSolution: l = ", l);
		TRACE("hensela::particularSolution: w = ", w);
		TRACE("hensela::particularSolution: N = ", N);
		TRACE("hensela::particularSolution: D = ", D);
		sol? => {
			v:VU := zero m;
			xk := monomial(1, k::Integer);
			xml := inv(monomial(1, l::Integer)::Fx);
			for j in 1..s repeat {
				res := ratrecon(w.j, xk, N, D);
				failed? res => return failed;
				v(Q j) := xml * retract res;
			}
			[v];
		}
		failed;
	}

	local padicSolution(A:M, b:V, n:I, m:I):(Boolean,I,I,I,I,I,V,I->I) == {
		import from F, FX, Integer;

		local D:I; local N:I;

		dA := degree A;
		db := degree b;

		B:M := zero(n, m);
		c := copy b;
		w:V := zero m;
		P:Permutation n := 1;
		Q:Permutation m := 1;
		s := k := l := 0@I;

		repeat {
			-- TEMPORARY: LOOP-INLINING BUG 1203
			-- for j in 1..s repeat {
			j:I := 1; while j <= s repeat {
				t := val0(c.j);
				w.j := add!(w.j, t, k::Integer);
				-- substract constant multiples of the first s
				-- colums of B from c, to make the first s
				-- entries of c divisible by x.
				for r in 1..n repeat c.r := c.r - t * B(r,j);
				j := next j;
			}

			i := next s;
			while i <= n and zero? val0(c.i) repeat i := next i;
			-- if all the entries of c equal 0 mod x we can
			-- improve the approximation by dividing c by x and
			-- incrementing k.  Then restart from the beginning.
			if i > n then {
				c := map!(divideByX)(c);
				k := next k;
				zero?(s) or k > N+D =>
					return(true, s, k, l, N, D,w,mapping Q);
			}
			-- otherwise we switch rows s+1 and s+i (cols 1 to s)
			-- with i the index of the first non zero entry of c;
			else {
				sb := next s;
				if i > sb then {
					rowSwap!(B, sb, i, 1, s);
					{ tmp:=c.sb; c.sb:=c.i; c.i:=tmp; }
					P := transpose!(P, sb, i);
				}
				-- TEMPORARY: LOOP-INLINING BUG 1203
				--for j in sb..m repeat B(sb,j) := A(P sb, Q j);
				j := sb; while j <= m repeat {
					B(sb,j) := A(P sb, Q j);
					j := next j;
				}
				cont?:Boolean := true;
				while cont? repeat {
					-- Here we substract constant multiples
					-- of the first s rows from (s+1)^{th}
					-- row to make its first s entries
					-- divisible by x.
					for ii in 1..s repeat {
						t := val0 B(sb,ii);
						c.sb := c.sb - t * c.ii;
						rowCombine!(B,1,sb, -t::FX, ii);
					}
					j := sb;
					while j <= m and zero? val0 B(sb,j)
							repeat j := next j;					
					cont? := j > m;
					-- if all entries in row s+1 of B are
					-- divisible by x, we multiply c and w
					-- by x, divide the (s+1)^{th} row by x
					-- and increment l.
					if cont? then {
						c := map!(multiplyByX)(c);
						w := map!(multiplyByX!)(w);
						c.sb := divideByX(c.sb);
						for r in 1..m repeat
						    B(sb,r):=divideByX B(sb,r);
						l := next l;
						l > sb * dA =>
							return(false, s, k,l,N,
								D, w,mapping Q);
					}
				}
				-- switch columns j and (s+1) of B (rows 1 to s)
				if j > sb then {
					Q := transpose!(Q, sb, j);
					colSwap!(B, sb, j, 1, s);
				}
				-- TEMPORARY: LOOP-INLINING BUG 1203
				-- for ii in sb+1..n repeat B(ii,sb):=A(P ii,Q sb);
				iii:=sb+1; while iii<=n repeat {
					B(iii,sb):=A(P iii,Q sb);
					iii := next iii;
				}
				-- Multiply the (s+1)^{th} row by a constant to
				-- make B(sb,sb) equal to 1 mod x. 
				t := val0 B(sb,sb);
				assert(~zero? t);
				it := inv t;
				c.sb := it * c.sb;
				-- TEMPORARY: LOOP-INLINING BUG 1203
				-- for r in 1..m repeat B(sb,r) := it * B(sb,r);
				rr:I:=1; while rr<=m repeat {
					B(sb,rr) := it * B(sb,rr);
					rr := next rr;
				}
				-- Substract constant multiples of row (s+1)
				-- from the first s rows to make the first s
				-- entries in column (s+1) divisible by x.
				-- TEMPORARY: LOOP-INLINING BUG 1203
				-- for ii in 1..s repeat {
				ii:I:= 1; while ii <= s repeat {
					t := val0 B(ii,sb);
					c.ii := c.ii - t * c.sb;
					rowCombine!(B, 1, ii, -t::FX, sb);
					ii := next ii;
				}
				-- increment s and restart from the top
				s := sb;
				N := (s-1) * dA + db;
				D := s * dA - l;
			}
		}
		never;
	}

	local ratrecon(u:FX, p:FX,N:I,D:I): Partial Fx == {
		import from FX, Fx, I, Integer;
		s0:FX := 0; t0:FX := 1;
		s1 := p; t1 := u rem p;
		while N < machine degree t1 repeat {
			(q,r1) := monicDivide(s1,t1);
			r0 := s0 - q*t0;
			(s0,s1):=(t0,t1);
			(t0,t1):=(r0,r1);
		}
		machine(degree(t0)) > D => failed;
		[t1/t0];
	}

	local degree(a:M):I == {
		import from Boolean, Integer, FX;
		maxdeg:I := 0;
		(n, m) := dimensions a;
		for i in 1..n repeat for j in 1..m repeat {
			if ~zero?(b := a(i, j))
				and (d := machine degree b) > maxdeg then
					maxdeg := d;
		}
		maxdeg;
	}

	local degree(v:V):I == {
		import from Boolean, Integer, FX;
		maxdeg:I := 0;
		for b in v | ~zero? b repeat {
			if (d := machine degree b) > maxdeg then maxdeg := d;
		}
		maxdeg;
	}
}

