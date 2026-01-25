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
------------------------------ sit_ffcycle.as ------------------------------
-- Copyright (c) Manuel Bronstein 1997
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1997
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I	== MachineInteger;
	Z	== Integer;
	V	== Vector;
	M	== DenseMatrix;
	ARR	== PrimitiveArray;
	Rp	== FractionBy(R, P, irr?);
}

#if ALDOC
\thistype{FractionFreeCyclicVector}
\History{Manuel Bronstein}{14/1/97}{created}
\Usage{import from \this(R, P, irr?)}
\Params{
{\em R} & \astype{IntegralDomain} & The coefficient domain\\
{\em P} & R & a nonzero nonunit of R\\
{\em irr?} & \astype{Boolean} &
Indicates whether P is known to be irreducible in R\\
}
\Descr{\this(R, P, irr?) provides linear algebra tools for fraction--free
computations of cyclic vectors and symmetric and exterior powers.}
\begin{exports}
\asexp{firstDependence}: &
\astype{DenseMatrix} \astype{FractionBy}(R, P, irr?) $\to$ \astype{Vector} R &
Dependence\\
\end{exports}
#endif

FractionFreeCyclicVector(R:IntegralDomain, P:R, irr?:Boolean): with {
	firstDependence: M Rp -> V R;
#if ALDOC
\aspage{firstDependence}
\Usage{\name~m}
\Signature{\astype{DenseMatrix} \astype{FractionBy}(R, P, irr?)}
{\astype{Vector} R}
\Params{
{\em m} & \astype{DenseMatrix} \astype{FractionBy}(R, P, irr?) & A matrix\\
}
\Descr{
Returns a vector {\em v} which contains the coefficients
of a dependence relation among the columns of {\em m}. The
relation is as small as possible, meaning that if {\em v} has
dimension {\em n} then the first $n-1$ columns of {\em m}
linearly independent over R.
There must be a relation between the columns of $m$.
Uses the optmizations described in:\\
M.~Bronstein, T.~Mulders \& J.A.~Weil,
{\em On symmetric powers of differential operators},
Proceedings of ISSAC'97, ACM Press (1997), 156--163.
}
#endif
} == add {
	local gcd?:Boolean	== R has GcdDomain;
	local decomp?:Boolean	== R has DecomposableRing;

	local primpart!(v:V R):V R == {
		gcd? => primpart0! v;
		v;
	}

	local rlcm(a:ARR R, n:I):R == {
		gcd? => rlcm0(a, n);
		1;
	}

	local removeRowContents!(mat:M R):M R == {
		gcd? => removeRowContents0! mat;
		mat;
	}

	-- returns the content of the j-th column of mat
	-- w = j-th column / returned content
	local vectorize!(w:V R, mat:M R, j:I, dim:I):R == {
		assert(numberOfRows mat = dim);
		gcd? => gcdvectorize!(w, mat, j, dim);
		for i in 1..dim repeat w.i := mat(i, j);
		1;
	}

	if R has GcdDomain then {
		local primpart0!(v:V R):V R == {
			import from Boolean, I, R;
			TIMESTART;
			g := v.1;
			for i in 2..#v repeat {
				unit? g => return v;
				g := gcd(g, v.i);
			}
			if ~unit? g then for i in 1..#v repeat
				v.i := quotient(v.i, g);
			TIME("ffcycle::primpart!: primitive part at ");
			v;
		}

		local removeRowContents0!(mat:M R):M R == {
			import from I;
			TIMESTART;
			(rs, cs) := dimensions mat;
			for i in 1..rs repeat removeRowContent!(mat, i, cs);
			TIME("ffcycle::removeRowContents!: done at ");
			mat;
		}

		local removeRowContent!(mat:M R, i:I, c:I):() == {
			import from Boolean, I, R;
			assert(c > 1);
			g := mat(i, 1);
			for j in 2..c repeat {
				unit? g => return;
				g := gcd(g, mat(i, j));
			}
			if ~unit? g then for j in 1..c repeat
				mat(i, j) := quotient(mat(i, j), g);
		}

		-- returns the content of the j-th column of mat
		-- w = j-th column / returned content
		local gcdvectorize!(w:V R, mat:M R, j:I, dim:I):R == {
			import from Boolean;
			assert(numberOfRows mat = dim);
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
				for i in 1..dim repeat w.i := quotient(w.i, g);
				g;
			}
			1;
		}

		local rlcm0(a:ARR R, n:I):R == {
			assert(n > 0);
			-- do not use the multiple lcm because we
			-- expect the elements of a to be constants
			-- in the cases where R is a polynomial ring
			-- import from List R;
			-- lcm [a.i for i in 0..prev n];
			l := a.0;
			for i in 1..prev n repeat l := lcm(l, a.i);
			l;
		}
	}

	-- returns a^0,...,a^N
	local powers(a:R, N:Z):ARR R == {
		import from I;
		pows:I := machine N;
		anu:ARR R := new next pows;
		anu.0 := 1;
		for i in 1..pows repeat anu.i := a * anu(prev i);
		anu;
	}

	local factors(p:R):List R == {
		decomp? => someFactors(p)$(R pretend DecomposableRing);
		[p];
	}

	-- given m = [u_0, u_1, ..., ], returns [a_0, a_1, ... , a_n ]
	-- such that a_0 u_0 + ... + a_n u_n = 0
	-- and there is no shorter dependence
	firstDependence(mat:M Rp):V R == {
		import from Boolean, I, Z, Rp, ARR R, ARR Z, ARR ARR R;
		import from ARR ARR Z, List R, LinearAlgebra(R, M R);
		import from M R;
		-- TRACE("ffcycle::firstDependence: mat = ", mat);
		TIMESTART;
		(rmat, cpi) := optimize mat;
		-- TRACE("ffcycle::firstDependence: rmat = ", rmat);
		TIME("ffcycle::firstDependence: optimized for p at ");
		nfac := #(lfac := factors P);
		vord:ARR ARR Z := new nfac;
		vfac:ARR R := new nfac;
		nfac := 0;
		for q in lfac | q ~= P repeat {
			vord.nfac := optimize!(rmat, q);
			vfac.nfac := q;
			nfac := next nfac;	-- number of factors optimized
		}
		TIME("ffcycle::firstDependence: optimized for factors at ");
		removeRowContents! rmat;
		-- TRACE("ffcycle::firstDependence: rmat = ", rmat);
		dim := numberOfRows mat;
		cont:ARR R := new next dim;
		gen := cyclicGen!(rmat, cont, dim);
		TRACE("ffcycle::firstDependence: ", "gen ready");
		mindep := firstDependence(gen, dim);
		-- TRACE("ffcycle::firstDependence: mindep = ", mindep);
#if TRACE
		import from String,TextWriter,Character,ExpressionTree;
		stderr << "mindep := ";
		maple(stderr, extree mindep);
		stderr << ":" << newline;
#endif
		TIME("ffcycle::firstDependence: dependence at ");
		-- the i-th coeff of the dependence  must be multiplied by
		--         P^{i-1 + cpi(i-1)} * */q^{vord(i-1)}
		-- where the product is taken over all q in vfac
		-- we can replace all those exponents e by e - min
		depsize := #mindep;
		assert(~zero?(mindep.depsize));
		pminexp := pmaxexp := cpi.0;
		vminexp:ARR Z := new nfac; vmaxexp:ARR Z := new nfac;
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for j in 0..prev nfac repeat {
		j:I := 0;
		while j < nfac repeat {
			vminexp.j := vmaxexp.j := vord.j.0;
			j := next j;
		}
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 1..prev depsize repeat {
		i:I := 1;
		while i < depsize repeat {
			nu := cpi.i + i::Z;
			if nu < pminexp then pminexp := nu;
			else if nu > pmaxexp then pmaxexp := nu;
			-- TEMPORARY: LOOP-INLINING BUG 1203
			-- for j in 0..prev nfac repeat {
			j := 0; while j < nfac repeat {
				nu := vord.j.i;
				if nu < vminexp.j then vminexp.j := nu;
				else if nu > vmaxexp.j then vmaxexp.j := nu;
				j := next j;
			}
			-- TEMPORARY: LOOP-INLINING BUG 1203
			i := next i;
		}
		pnu := powers(P, pmaxexp - pminexp);
		qnu:ARR ARR R := new nfac;
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for j in 0..prev nfac repeat {
		j := 0; while j < nfac repeat {
			qnu.j := powers(vfac.j, vmaxexp.j - vminexp.j);
			j := next j;
		}
		-- if R is a Gcd Domain, then we must additionallu multiply
		-- the i-th coeff by lcm(cont.0,...,cont(depsize-1)) / cont(i-1)
		lmcont := rlcm(cont, depsize);
		Ln:V R := zero depsize;
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 1..depsize | ~zero?(mindep.i) repeat {
		i := 1; while i <= depsize repeat {
			if ~zero?(mindep.i) then {
			i1 := prev i;
			expon := cpi.i1 + i1::Z - pminexp;
			assert(expon >= 0);
			coeff := pnu(machine expon);
			-- TEMPORARY: LOOP-INLINING BUG 1203
			-- for j in 0..prev nfac repeat {
			j := 0; while j < nfac repeat {
				expon := vord.j.i1 - vminexp.j;
				assert(expon >= 0);
				coeff := coeff * qnu(j)(machine expon);
				j := next j;
			}
			if gcd? then coeff := quotient(lmcont, cont.i1) * coeff;
			Ln.i := coeff * mindep.i;
			}
			-- TEMPORARY: LOOP-INLINING BUG 1203
			i := next i;
		}
		TIME("ffcycle::firstDependence: non-primitive operator at ");
		primpart! Ln;
	}

	-- computes the shifts to apply to each row and column in order
	-- to minimize the order at p of the eventual matrix entries
	-- returns the shifted matrix over R and the array of column shifts
	local orderp(x:Rp):Partial I == {
		import from Z;
		zero? x => failed;
		[machine order x];
	}

#if TRACE
	local trace(a:ARR Z, n:I):() == {
		import from TextWriter, Character, String, Z;
		for i in 0..prev n repeat stderr << a.i << " ";
		stderr << newline;
	}
#else
	local trace(a:ARR Z, n:I):() == n;
#endif
	local optimize(mat:M Rp):(M R, ARR Z) == {
		import from I, Z, Rp, ARR Z, OptimizeSymmetricPower(Rp, M Rp);
		-- TRACE("ffcycle::optimize: mat = ", mat);
		(rs, cs) := dimensions mat;
		(rshift, cshift, optimum) := optimize(mat, orderp);
		TRACE("ffcycle::optimize: optimum = ", optimum);
		trace(rshift, rs);
		trace(cshift, cs);
		rmat:M R := zero(rs, cs);
		for i in 1..rs repeat for j in 1..cs repeat {
			c := shift(mat(i, j), rshift(prev i) + cshift(prev j));
			assert(one? denominator c);
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
			[machine nu x];
		}
	}

	local optimize!(mat:M R, a:R):ARR Z == {
		import from Boolean, I, Z, R, Partial R, ARR Z, ARR R;
		import from OptimizeSymmetricPower(R, M R);
		(rs, cs) := dimensions mat;
		(rshift, cshift, optimum) := optimize(mat, uorder a);
		maxexp:Z := 0;
		for i in 1..rs repeat for j in 1..cs repeat {
			if ~zero?(c := mat(i, j)) then {
				s := abs(rshift(prev i) + cshift(prev j));
				if s > maxexp then maxexp := s;
			}
		}
		anu := powers(a, maxexp);	-- a^0 .. a^maxexp
		for i in 1..rs repeat for j in 1..cs repeat {
			if ~zero?(c := mat(i, j)) then {
				s := rshift(prev i) + cshift(prev j);
				assert(abs(s) <= maxexp);
				ap := anu(machine abs s);	-- a^|s|
				if s >= 0 then mat(i, j) := ap * c;
				else {
					assert(~failed? exactQuotient(c, ap));
					mat(i, j) := quotient(c, ap);
				}
			}
		}
		cshift;
	}


	local cyclicGen!(mat:M R, cont:ARR R, dim:I):Generator V R == generate {
		w:V R := zero dim;
		for j in 1..numberOfColumns mat repeat {
			cont(prev j) := vectorize!(w, mat, j, dim);
#if TRACE
			import from String,TextWriter,Character,ExpressionTree;
			stderr << "w := ";
			maple(stderr, extree w);
			stderr << ":" << newline;
#endif
			yield w;
		}
	}
}
