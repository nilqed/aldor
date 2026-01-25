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
------------------------------ ffcyclicvec.as ------------------------------
#include "sumit"

macro {
	I	== SingleInteger;
	Z	== Integer;
	V	== Vector;
	M	== DenseMatrix;
	ARR	== PrimitiveArray;
	LA	== LinearAlgebra;
	FFGE	== TwoStepFractionFreeGaussElimination;
	-- FFGE	== FractionFreeGaussElimination;
	Rp	== QuotientBy(R, P, false);
}

FractionFreeCyclicVector(R:IntegralDomain,
	L:LinearOrdinaryDifferentialOperatorCategory0 R, P:R): with {
		firstAnnihilator: M Rp -> L;
		firstAnnihilator: (M R, V R) -> (L, M R);
} == add {
	local gcd?:Boolean == R has GcdDomain;

	-- returns (a_0 + a_1 D + ... + a_n D^n, [u_0, u_1, ..., u_{n-1}])
	-- such that a_0 u_0 + ... + a_n u_n = 0
	-- where u_{i+1} = P u_i' - A u_i - i P' u_i
	-- and there is no shorter dependence
	firstAnnihilator(A:M R, v:V R):(L, M R) == {
		import from I, Z, Rp, V Rp, M Rp, Derivation R, Derivation Rp;
		vp:V Rp := zero(dim := #v);
		for i in 1..dim repeat vp.i := normalize(v.i :: Rp);
		D := derivation$L;
		mat := makeMatrix(D(P)::Rp, connection(lift D, A), vp);
		n := retract degree(op := firstAnnihilator mat);
		B:M R := zero(dim, n);
		ASSERT(n <= dim);
		for i in 1..dim repeat {
			for j in 1..n repeat {
				ASSERT(one? denominator mat(i, j));
				B(i, j) := numerator mat(i, j);
			}
		}
		(op, B);
	}

	local connection(D:Derivation Rp, A:M R):(V Rp -> V Rp) == {
		import from I, Z, Rp, V Rp, M Rp;
		n := rows A;
		ASSERT(n = cols A);
		Ap:M Rp := zero(n, n);
		for i in 1..n repeat
			for j in 1..n repeat
				Ap(i, j) := - normalize(A(i, j)::Rp);
		(v:V Rp):V Rp +-> {
			w := Ap * v;
			for i in 1..#w repeat w.i := shift(D(v.i), 1) + w.i;
			w;
		}
	}

	-- D is already p times the connection
	local makeMatrix(Dp:Rp, D:V Rp -> V Rp, v:V Rp):M Rp == {
		import from I, Z;
		nu:Z := 0;
		dim := #v;
		mat := zero(dim, next dim);
		for i in 1..dim repeat {
			vectorize!(mat, i, v);
			Dv := D v;	-- always a new copy
			v := add!(Dv, times!(nu * Dp, v));
			nu := prev nu;
		}
		vectorize!(mat, next dim, v);
		mat;
	}

	local vectorize!(mat:M Rp, j:I, v:V Rp):() == {
		dim := rows mat;
		for i in 1..dim repeat mat(i, j) := v.i;
	}

	if R has GcdDomain then {
		local primpart(op:L):L == {
			START__TIME;
			op := primitivePart op;
			TIME("primpart: primitive part at ");
			op;
		}

		local removeRowContents!(mat:M R):() == {
			import from I;
			START__TIME;
			(rs, cs) := dimensions mat;
			for i in 1..rs repeat removeRowContent!(mat, i, cs);
			TIME("ffsympow::removeRowContents: done at ");
		}

		local removeRowContent!(mat:M R, i:I, c:I):() == {
			ASSERT(c > 1);
			g := mat(i, 1);
			for j in 2..c repeat {
				unit? g => return;
				g := gcd(g, mat(i, j));
			}
			if ~unit? g then {
				for j in 1..c repeat
					mat(i, j) := quotient(mat(i, j), g);
			}
		}

		-- returns the content of the j-th column of mat
		-- w = j-th column / returned content
		local gcdvectorize!(w:V R, mat:M R, j:I, dim:I):R == {
			ASSERT(rows mat = dim);
			g := w.1 := mat(1, j);
			noinv? := ~unit? g;
			for i in 2..dim repeat {
				w.i := mat(i, j);
				if noinv? then {
					g := gcd(g, w.i);
					noinv? := ~unit? g;
				}
			}
			noinv? => {	-- non trivial gcd
				for i in 1..dim repeat
					w.i := quotient(w.i, g);
				g;
			}
			1;
		}

		local rlcm(a:ARR R, n:I):R == {
			ASSERT(n > 0);
			-- do not use the multiple lcm because we
			-- expect the elements of a to be constants
			-- in the cases where R is a polynomial ring
			-- import from List R;
			-- lcm [a.i for i in 1..n];
			l := a.1;
			for i in 2..n repeat l := lcm(l, a.i);
			l;
		}
	}

	-- returns a^0,...,a^N
	local powers(a:R, N:Z):ARR R == {
		pows:I := next retract N;
		anu:ARR R := new pows;
		anu.1 := 1;
		for i in 2..pows repeat anu.i := a * anu(prev i);
		anu;
	}

	firstAnnihilator(mat:M Rp):L == {
		import from I,Z,Rp,V R,ARR R,ARR Z,ARR ARR R, ARR ARR Z, List R;
		START__TIME;
		(rmat, cpi) := optimize mat;
		TIME("annihilator::symmetricPower: optimized for p at ");
		nfac := #(lfac := exactFactors P);
		vord:ARR ARR Z := new nfac;
		vfac:ARR R := new nfac;
		nfac := 1;
		for q in lfac | q ~= P repeat {
			vord.nfac := optimize!(rmat, q);
			vfac.nfac := q;
			nfac := next nfac;
		}
		nfac := prev nfac;	-- number of factors optimized
		TIME("annihilator: optimized for factors at ");
		if gcd? then removeRowContents! rmat;
		dim := rows mat;
		cont:ARR R := new next dim;
		gen := cyclicGen!(rmat, cont, dim);
		mindep := firstDependence(gen, dim)$LA(R, M R, FFGE(R, M R));
		TIME("annihilator: dependence at ");
		-- the i-th coeff of the dependence must be multiplied by
		--         P^{i-1 + cpi.i} * */q^{ordq.i}
		-- where the product is taken over all q in vfac
		-- we can replace those exponents e by e - min
		depsize := #mindep;
		ASSERT(~zero?(mindep.depsize));
		pminexp := pmaxexp := cpi.1;
		vminexp:ARR Z := new nfac; vmaxexp:ARR Z := new nfac;
		for j in 1..nfac repeat vminexp.j := vmaxexp.j := vord.j.1;
		for i in 2..depsize repeat {
			nu := cpi.i + prev(i)::Z;
			if nu < pminexp then pminexp := nu;
			else if nu > pmaxexp then pmaxexp := nu;
			for j in 1..nfac repeat {
				nu := vord.j.i;
				if nu < vminexp.j then vminexp.j := nu;
				else if nu > vmaxexp.j then vmaxexp.j := nu;
			}
		}
		pnu := powers(P, pmaxexp - pminexp);
		qnu:ARR ARR R := new nfac;
		for j in 1..nfac repeat
			qnu.j := powers(vfac.j, vmaxexp.j - vminexp.j);
		-- if R is a Gcd Domain, then we must additionallu multiply
		-- the i-th coeff by lcm(cont.1,...,cont.depsize) / cont.i
		lmcont:R := { gcd? => rlcm(cont, depsize); 1 }
		-- go in descending order to avoid quadratic space alloc
		Ln:L := 0;
		for i in depsize..1 by -1 | ~zero?(mindep.i) repeat {
			expon := cpi.i + prev(i)::Z - pminexp;
			ASSERT(expon >= 0);
			coeff := pnu(next retract expon);
			for j in 1..nfac repeat {
				expon := vord.j.i - vminexp.j;
				ASSERT(expon >= 0);
				coeff := coeff * qnu(j)(next retract expon);
			}
			if gcd? then coeff := quotient(lmcont, cont.i) * coeff;
			Ln := add!(Ln, coeff * mindep.i, prev(i)::Z);
		}
		TIME("annihilator: non-primitive operator at ");
		gcd? => primpart Ln;
		Ln;
	}

	-- computes the shifts to apply to each row and column in order
	-- to minimize the order at p of the eventual matrix entries
	-- returns the shifted matrix over R and the array of column shifts
	local orderp(x:Rp):Partial I == {
		import from Z;
		zero? x => failed;
		[retract order x];
	}
	local optimize(mat:M Rp):(M R, ARR Z) == {
		import from I, Z, Rp, ARR Z, Optimize(Rp, M Rp);
		(rs, cs) := dimensions mat;
		(rshift, cshift, optimum) := optimize(mat, orderp);
		rmat:M R := zero(rs, cs);
		for i in 1..rs repeat for j in 1..cs repeat {
			c := shift(mat(i, j), rshift.i + cshift.j);
			ASSERT(one? denominator c);
			rmat(i, j) := numerator c;
		}
		(rmat, cshift);
	}

	-- computes the shifts to apply to each row and column in order
	-- to minimize the order at a of the eventual matrix entries
	-- shifs the matrix and return the array of column shifts
	local uorder(a:R):R -> Partial I == {
		import from Z;
		nu := order a;
		(x:R):Partial I +-> {
			zero? x => failed;
			[retract nu x];
		}
	}

	local optimize!(mat:M R, a:R):ARR Z == {
		import from I, Z, R, Partial R, ARR Z, ARR R, Optimize(R, M R);
		(rs, cs) := dimensions mat;
		(rshift, cshift, optimum) := optimize(mat, uorder a);
		maxexp:Z := 0;
		for i in 1..rs repeat for j in 1..cs repeat {
			if ~zero?(c := mat(i, j)) then {
				s := abs(rshift.i + cshift.j);
				if s > maxexp then maxexp := s;
			}
		}
		anu := powers(a, maxexp);	-- a^0 .. a^maxexp
		for i in 1..rs repeat for j in 1..cs repeat {
			if ~zero?(c := mat(i, j)) then {
				s := rshift.i + cshift.j;
				ASSERT(abs(s) <= maxexp);
				ap := anu(next retract abs s);	-- a^|s|
				if s >= 0 then mat(i, j) := ap * c;
				else {
					ASSERT(~failed? exactQuotient(c, ap));
					mat(i, j) := quotient(c, ap);
				}
			}
		}
		cshift;
	}


	local cyclicGen!(mat:M R, cont:ARR R, dim:I):Generator V R == generate {
		w:V R := zero dim;
		for j in 1..cols mat repeat {
			cont.j := vectorize!(w, mat, j, dim);
#if ASTRACE
			import from ExpressionTree;
			print << "w := ";
			maple(print, extree w);
			print << ":" << newline;
#endif
			yield w;
		}
	}

	-- returns the content of the j-th column of mat
	-- w = j-th column / returned content
	local vectorize!(w:V R, mat:M R, j:I, dim:I):R == {
		ASSERT(rows mat = dim);
		gcd? => gcdvectorize!(w, mat, j, dim);
		for i in 1..dim repeat w.i := mat(i, j);
		1;
	}
}
