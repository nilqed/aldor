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
------------------------------ sysholonom.as --------------------
--
-- Copyright Manuel Bronstein, 1997-1998
-- Copyright INRIA, 1998

#include "sumit"

#if ASDOC
#endif

macro {
	I	== SingleInteger;
	Z	== Integer;
	Q	== Quotient Z;
	ARR	== PrimitiveArray;
	Rxe	== LinearOrdinaryDifferenceOperator(R, Rx);
	M	== DenseMatrix;
}

FirstOrderHolonomicRecurrenceSystem(R:CommutativeRing,
	Rx:UnivariatePolynomialCategory R): SumitType with {
		degree: % -> Z;
		if R has Field then fill!: (%,ARR I,I) -> (ARR M R, I, I) -> ();
		if R has IntegralDomain then indicialEquation: % -> Rx;
		matrix: % -> M Rx;
		operator: % -> Rxe;
		reductum: (%, ARR I, I) -> (ARR M R, I) -> M R;
		shift: (Rxe, Z, M Rx) -> %;
		trailingDegree: % -> Z;
		if R has Join(IntegralDomain, RationalRootRing) then
			degreeBound:% -> Partial Integer;
	} == add {
		-- The recurrence is stored as [R(E) E^exp, A(x), d]
		-- where the coefficient of degree 0 of R(E) is nonzero.
		-- and d = max(deg(A_ij(x)))
		-- the differential system is p(x) Y' = A(x) Y
		-- where p(0) <> 0, which implies that deg(p) = deg(oper)
		-- the recurrence is applied as follows:
		--   p_e(N-B) Y_N =
		--              A_0 Y_{N-1} + ... + A_d Y_{N-(d+1)}
		--   - p_{e-1}(N-B) Y_{N-1} - ... - p_0(N-B) Y_{N-e}
		-- where R(E) = p_0 + p_1 E + ... + p_e E^e
		--       A(x) = A_0 + A_1 x + ... + A_d x^d
		--   and B    = e + exp
		--  (currently e = order of differential operator
		--         and exp = 1 - e, which implies that B = 1)
		macro Rep == Record(oper:Rxe, exponent:Z, mat:M Rx, dmat:I);

		local field?:Boolean	== R has Field;
		trailingDegree(L:%):Z	== { import from Rep; rep(L).exponent; }
		operator(L:%):Rxe	== { import from Rep; rep(L).oper;}
		matrix(L:%):M Rx	== { import from Rep; rep(L).mat;}
		local matdegree(L:%):I	== { import from Rep; rep(L).dmat; }

		if R has IntegralDomain then {
			indicialEquation(L:%):Rx == {
				import from I, Z, Rxe, M R, M Rx;
				d := matdegree L;
				e := prev opdegree L;
				d < e => monom;		-- no nonconst. sols
				a := leadingMatrix L;
				(r, c) := dimensions a;
				d > e => {	-- a = A_d is trailing
					rank a = c => monom;
					0;	-- no info: system is not simple
				}
		-- in the case d = e, the trailing matrix of the recurrence is
		-- m(N) = A_d - p_0(N)      and one has m(N-B) Y_deg = 0
		-- where deg is the degree of the poly sol,
		--   N = deg + d + 1  and  B = opdegree + trailingDegree
		-- so the indicial equation for deg is the determinant of
		--    A_d - p_0(deg + d + 1 - B)
				m:M Rx := zero(r, c);
				for i in 1..r repeat for j in 1..c repeat
					m(i, j) := a(i, j)::Rx;
				p := coefficient(operator L, 0);	-- p_0
				B := opdegree L + retract trailingDegree L;
				p := compose(p, monom + (next(d) - B)::Rx);
				ASSERT(r = c);
				for i in 1..r repeat m(i, i) := m(i, i) - p;
				determinant m;
			}

			if R has RationalRootRing then {
				degreeBound(L:%):Partial Z == {
					import from Rx, RationalRoot;
					import from List RationalRoot;
					zero?(eq:=indicialEquation L) => failed;
					TRACE("sysholonom:indicial eq. = ", eq);
					d:Z := 0;
					for rt in integerRoots eq repeat {
						if (m := integerValue rt) > d
							then d := m;
					}
					[d];
				}
			}
		}

		-- returns the leading coeffs of the highest degree terms of A
		local leadingMatrix(L:%):M R == {
			import from I, Z, Rx, M Rx;
			d := matdegree(L)::Z;
			(r, c) := dimensions(a := matrix L);
			m:M R := zero(r, c);
			for i in 1..r repeat for j in 1..c repeat {
				if (~zero?(b := a(i, j))) and degree b = d then
					m(i, j) := leadingCoefficient b;
			}
			m;
		}

		degree(L:%):Z == {
			import from I;
			max(opdegree L, next matdegree L)::Z;
		}

		local opdegree(L:%):I == {
			import from Z, Rxe;
			retract degree operator L;
		}

		local recur(L:Rxe, n:Z, m:M Rx):% == {
			import from Rep;
			per [L, n, m, degree m];
		}

		sample:% == {
			import from I, Z, Rxe, M Rx, Rep;
			-- CAUSES A RUNTIME SEG FAULT WITH THE 1.10.a COMPILER
			-- shift(1, 0, zero(1, 1));
			per [1, 0, zero(1, 1), 0];
		}

		extree(L:%):ExpressionTree == {
			import from Rxe;
			extree operator L;
		}

		(L1:%) = (L2:%):Boolean == {
			import from Z, Rxe, M Rx;
			operator L1 = operator L2
				and trailingDegree L1 = trailingDegree L2
				and matrix L1 = matrix L2;
		}

		-- return L(E) E^n
		shift(L:Rxe, n:Z, m:M Rx):% == {
			(a, e) := trailingMonomial L;
			if e > 0 then L := shft(L, -e);
			recur(L, e + n, m);
		}

		-- return L(E) E^n
		local shft(L:Rxe, n:Z):Rxe == {
			s:Rxe := 0;
			for term in L repeat {
				(c, e) := term;
				ASSERT(0 <= e + n);
				s := add!(s, c, e + n);
			}
			s;
		}

		-- returns the dot product
		-- (c.1(n),...,c.nu(n)) . (a_m,...,a_(m+nu-1))
		-- where a_i is stored in a[i]
		-- l indicates which rows need to be computed
		local dot(c:ARR Rx,n:R, a:ARR M R, m:I, nu:I, l:List I):M R == {
			import from Rx;
			(r, cl) := dimensions(a.1);
			ans:M R := zero(r, cl);
			start := 1 - min(m, 0);
			for k in start..nu repeat {
				ck := (c.k)(n);
				if ~zero?(ck) then {
					A := a(m + k);
					for i in l repeat for j in 1..cl repeat
						ans(i, j) := add!(ans(i, j),
								ck * A(i, j));
				}
			}
			ans;
		}

		-- subtracts from each mt(r, j)
		--    [p.f,...,p.t] . [a(m+f)(i,j),...,a(m+f+t)(i,j)]
		-- where p.k is the coefficient of p in x^(t-k)
		local sub!(mt:M R,r:I,c:I,p:Rx,f:I,t:I,a:ARR M R,m:I,i:I):()=={
			import from R;
			for term in p repeat {
				(cf, e) := term;
				ASSERT(~zero? cf);
				k := t - retract e;
				if k >= f then for j in 1..c repeat
					mt(r,j) := mt(r,j) - cf * a(m+k)(i,j);
			}
		}

		-- returns mt minus the dot product
		--  (c_0,...,c.nu) . (a_(m+nu-1),...,a_(m-1))
		-- where c.i is the matrix of coefficients of x^i in c
		-- l indicates which rows need to be computed
		local dot!(mt:M R,c:M Rx,a:ARR M R,m:I,nu:I,l:List I):M R == {
			frm := 1 - min(m, 0);
			cl := cols mt;
			for i in l repeat for j in 1..cl repeat
				sub!(mt, i, cl, c(i, j), frm, nu, a, m, j);
			mt;
		}

		-- returns the highest degree among the entries
		local degree(a:M Rx):I == {
			import from I, Z, Rx;
			(r, c) := dimensions a;
			ASSERT(r > 0); ASSERT(c > 0);
			d:Z := 0;
			for i in 1..r repeat for j in 1..c repeat {
				p := a(i, j);
				if (~zero? p) and ((dg := degree p) > d) then
					d := dg;
			}
			retract d;
		}

		-- reductum and denom return m and d such that
		-- a_N = -m/d, assuming that a_i is stored in a[i+1]
		-- do not compute row i beyond a_{bds.i + p} for each i
		reductum(rec:%, bds:ARR I, p:I):(ARR M R, I) -> M R == {
			import from Bits, I, List I, R, Z, Rxe, ARR Rx;
			nu := opdegree rec;
			TRACE("sysholonom::reductum, nu = ", nu);
			c:ARR Rx := new(nu, 0);
			for term in reductum operator rec repeat {
				(cf, e) := term;
				c(retract next e) := cf;
			}
			m := matdegree rec;
			TRACE("sysholonom::reductum, m = ", m);
			mat := matrix rec;
			cut:ARR I := new(rm := rows mat);
			for i in 1..rm repeat cut.i := bds.i + p;
			B := nu + retract trailingDegree rec;
			TRACE("sysholonom::reductum, B = ", B);
			m1 := next m;
			-- assumes that it will be called with increasing N's
			-- since it side-effects lrows
			(a:ARR M R, N:I):M R +-> {
				START__TIME;
				TRACE("sysholonom::reductum, N = ", N);
				ASSERT(N >= B);
				-- remove rows whose cutoff is < N
				lrows := [i for i in 1..rm | N <= cut.i];
				mm := dot(c, (N - B)::R, a, N - nu, nu, lrows);
				TIME("reductum: dot at ");
				TRACE("sysholonom::reductum, mm = ", mm);
				mm := dot!(mm, mat, a, N - m1, m1, lrows);
				TIME("reductum: dot! at ");
				TRACE("sysholonom::reductum, mm = ", mm);
				mm;
			}
		}

		local denom(rec:%):I -> R == {
			import from Z, Rx, Rxe;
			p := leadingCoefficient operator rec;
			B := opdegree rec + retract trailingDegree rec;
			(N:I):R +-> p((N-B)::R);
		}

		if R has Field then {
			-- compute a_frm to a_two using L
			-- a_0 is the first value, which is stored in a[1]
			-- stores a 0 when a singularity is encountered
			-- do not compute row i beyond a_{bds.i + p} for each i
			fill!(rec:%, bds:ARR I, p:I):(ARR M R, I, I) -> () == {
				num := reductum(rec, bds, p);
				den := denom rec;
				(r, c) := dimensions matrix rec;
				(a:ARR M R, frm:I, two:I):() +-> {
					import from R, M R;
					for N in frm..two repeat {
						N1 := next N;
						d := den N;
						if zero? d then
							a.N1 := zero(r, c);
						else {
							n := num(a, N);
							a.N1 := (- inv d) * n;
						}
					}
				}
			}
		}
}
