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
------------------------------ sit_sys1pol.as ------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	B == Boolean;
	I == MachineInteger;
	Z == Integer;
	V == Vector;
	A == Array;
	M == DenseMatrix;
	PFX == Partial FX;
	SYS == LinearOrdinaryFirstOrderSystem;
	RXE == LinearOrdinaryRecurrence(R, RX);
}

#if ALDOC
\thistype{LinearOrdinaryFirstOrderSystemPolynomialSolutions}
\History{Manuel Bronstein}{12/10/2000}{created}
\Usage{import from \this(R, F, $\iota$, RX, RXY, FX)}
\Params{
{\em R} & \astype{IntegralDomain} & An integral domain\\
{\em F} & \astype{Field} & A field containing R\\
$\iota$ & $R \to F$ & Injection from R into F\\
{\em RX} & \astype{UnivariatePolynomialCategory} R & Polynomials over R\\
{\em RXY} & \astype{UnivariateSkewPolynomialCategory} RX & Operators over RX\\
{\em FX} & \astype{UnivariateFreeFiniteAlgebra} F & Polynomials over F\\
         & \astype{CommutativeRing} &\\
}
\Descr{\this(R, F, $\iota$, RX, FX) provides a polynomial solver
for first order linear ordinary differential or recurrence systems with
polynomial coefficients.}
\begin{exports}
\asexp{kernel}:
& (SYS RX, \astype{Integer}) $\to$ \astype{DenseMatrix} FX &
Polynomial solutions\\
\end{exports}
\begin{exports}[if $R$ has \astype{RationalRootRing} then]
\asexp{degreeBound}: & SYS RX $\to$ \astype{Integer} & Degree bound\\
\asexp{kernel}: & SYS RX $\to$ \astype{DenseMatrix} FX & Polynomial solutions\\
\end{exports}
\begin{aswhere}
SYS &==& \astype{LinearOrdinaryFirstOrderSystem}\\
\end{aswhere}
#endif

LinearOrdinaryFirstOrderSystemPolynomialSolutions(R:IntegralDomain,
		F:Field, inj: R -> F,
		RX: UnivariatePolynomialCategory R,
		RXY:UnivariateSkewPolynomialCategory RX,
		FX: Join(CommutativeRing, UnivariateFreeFiniteAlgebra F)):with {
			if R has RationalRootRing then {
				degreeBound: SYS RX -> Z;
#if ALDOC
\aspage{degreeBound}
\Usage{\name~L}
\Signature{\astype{LinearOrdinaryFirstOrderSystem} RX}{\astype{Integer}}
\Params{
{\em L} & \astype{LinearOrdinaryFirstOrderSystem} RX &
A first order recurrence system\\
}
\Retval{Returns an upper bound for the degree of any polynomial solution
of $LY = 0$, $-1$ if there are no nonzero polynomial solution.}
#endif
				kernel: SYS RX -> M FX;
			}
			kernel: (SYS RX, Z) -> M FX;
#if ALDOC
\aspage{kernel}
\Usage{\name~L\\ \name(L, n)}
\Signatures{
\name: & SYS RX $\to$ \astype{DenseMatrix} FX\\
\name: & (SYS RX, \astype{Integer}) $\to$ \astype{DenseMatrix} FX\\
}
\begin{aswhere}
SYS &==& \astype{LinearOrdinaryFirstOrderSystem}\\
\end{aswhere}
\Params{
{\em L} & SYS RX &
A linear ordinary first order differential or difference system\\
{\em n} & \astype{Integer} & A degree bound (optional)\\
}
\Descr{\name(L) returns a matrix whose columns for a
basis for all the polynomial solutions of $Ly = 0$, while
\name(L,n) returns a matrix whose columns form a
basis for the polynomial solutions of $LY = 0$
of degree at most $n$.}
\Remarks{\name(L) is available only if R has \astype{RationalRootRing}.
The type of system (differential or difference) is determined from
the parameter RXY to the domain.
Produces an error if RXY is neither a differential or recurrence
operator type. The polynomials in the kernel are expressed in terms of
the basis $P_n$ described in
\asfunc{LinearOrdinaryOperatorToRecurrence}{recurrence}.}
#endif
} == add {
	kernel(L:SYS RX, bound:Z):M FX == {
		import from B, I;
		(hom, part) := solve!(L, bound, zero(0, 0), true);
		assert(zero? numberOfColumns part);
		hom;
	}

	-- homsols? is true if a basis of the kernel is also wanted
	-- always returns (zero(*,0), partsol) if homsols? is false
	local solve!(L:SYS RX, bound:Z, g:M FX, homsols?:B):(M FX, M FX) == {
		import from I;
		import from LinearOrdinaryOperatorToRecurrence(R, RX, RXY, RXE);
		n := machine order L;
		assert(n > 0);
		bound < 0 => (zero(n, 0), zero(n, numberOfColumns g));
		(r, e) := recurrence L;
		solve(r, e, n, bound, g, homsols?);
	}

	local forever(g:Generator F):Generator F == generate {
		import from F;
		for x in g repeat yield x;
		repeat yield 0;
	}

	local coefficients(g:V FX):Generator V F == generate {
		import from I, FX, Generator F;
		a:PrimitiveArray Generator F := new(n := #g);
		n1 := prev n;
		for i in 0..n1 repeat a.i := forever coefficients g(next i);
		v:V F := zero n;
		repeat {
			for i in 0..n1 repeat v(next i) := next!(a.i);
			yield v;
		}
	}

	-- simultaneous solving of several right-hand-sides with common bound
	-- the real recurrence is L E^e
	-- n = order of original operator, bound = degree bound on solution
	-- homsols? is true if a basis of the kernel is also wanted
	-- always returns (empty, partsol) if homsols? is false
	-- if col(g,i) <> 0 then col(partsol,i) = 0 means no particular solution
	-- if col(g,i) == 0 then col(partsol,i) is automatically 0
	-- TEMPORARY: ONLY HOMOGENEOUS SYSTEMS FOR NOW
	local solve(L:A M RX,e:Z,n:I,bound:Z,g:M FX, homsols?:B):(M FX,M FX)=={
                -- If e > 0, then any vector of polynomials of degrees at
                -- most e-1 is also a homogeneous solution
                -- Since there are n linearly independent homogeneous solutions,
                -- this implies that e = 1 and that the homogeneous solutions
                -- are all the constant vectors.
		homsols? and e > 0 => {
			assert(one? e);
			-- TEMPORARY (solve doesn't do inhomogeneous for now)
			-- (ignore,partsol) := solve1(r, e, n, bound, g, false);
			partsol:M FX := zero(n, 0);
			(one n, partsol);
		}
		solve1(L, e, n, bound, g, homsols?);
	}

	local solve1(L:A M RX,e:Z,n:I,bound:Z,g:M FX, homsols?:B):(M FX,M FX)=={
		import from RX, FX, F, V F, V V F, LinearAlgebra(F, M F);
		import from UnivariatePolynomialCRTLinearAlgebra(R, RX, M RX);
		import from LinearOrdinaryRecurrenceSystemTools(R, F, inj, RX);
		TRACE("sys1pol::solve: recurrence = ", L);
		TRACE("sys1pol::solve: e = ", e);
		TRACE("sys1pol::solve: n = ", n);
		TRACE("sys1pol::solve: bound = ", bound);
		TIMESTART;
		nrhs := numberOfColumns g;
		bound < 0 => (zero(n, 0), zero(n, nrhs));
		assert(e <= 0 or ~homsols?);
		inhom? := ~zero? g;
		assert(~inhom?);	-- TEMPORARY (HOMOGENEOUS)
		-- exit if g = 0 and the homogeneous sols were not requested
		~(inhom? or homsols?) => (zero(n, 0), zero(n, nrhs));
		m := #L;
		maxsing := machine degreeBound L(prev m);
		sing:PrimitiveArray I := new next maxsing;
		constraints:V M F := zero maxsing;
		local kh:Stream V V F;
		kh := [kernel(L, e, sing, constraints)];
		TIME("sys1pol::solve: solution stream set at ");
		N := machine bound;
		-- forces all terms to be computed up to N+m
		w := kh(N+m);
		TIME("sys1pol::solve: solution stream computed at ");
		nsing := sing.0;	-- number of singularities crossed
		TRACE("sys1pol::solve: nsing = ", nsing);
		assert(0 <= nsing); assert(nsing <= maxsing);
		nconstr:I := 0;		-- count number of linear constraints
		for i in 1..nsing repeat
			nconstr := nconstr + numberOfRows(constraints.i);
		TRACE("sys1pol::solve: nconstr = ", nconstr);
		sys:M F := zero(n * m + nconstr, #w);
		for i in 1..m repeat {	-- beyond degree bound ==> 0 or -rh
			ni := n * prev i;
			v := kh(N+i);
			assert(#v <= #w);
			for j in 1..#v repeat {
				vj := v.j;
				for k in 1..n repeat sys(k + ni, j) := vj.k;
			}
		}
		index := next(n * m);
		for i in 1..nsing repeat {	-- singular constraints
			constr := constraints.i;
			(rconstr, cconstr) := dimensions constr;
			assert(cconstr <= #w);
			for k in 1..rconstr repeat {
				for j in 1..cconstr repeat
					sys(index, j) := constr(k, j);
				index := next index;
			}
		}
		TIME("sys1pol::solve: linear system set at ");
		-- TRACE("sys1pol::solve: sys = ", sys);
		sol:M F := zero(0, 0);
		psol?:PrimitiveArray B := new nrhs;
		psol1? := false;
		assert(homsols?);
		sol := kernel sys;
		TIME("sys1pol::solve: linear system solved at ");
		polker:M FX := zero(n, d := numberOfColumns sol);
		partsol:M FX := zero(n, nrhs);
		-- compute the solutions by descending order of degree
		buffer:V F := zero n;
		if d > 0 or psol1? then for i in N..0 by -1 repeat {
			ii := i::Z;
			v := kh.i;
			for j in 1..d repeat
				add!(polker, j, dot!(buffer, sol, j, v), ii);
		}
		TIME("sys1pol::solve: polynomial solutions at ");
		TRACE("sys1pol::solve: polker = ", polker);
		(polker, partsol);
	}

	-- add v x^n to j-th column of m
	local add!(m:M FX, j:I, v:V F, n:Z):() == {
		import from FX;
		r := numberOfRows m;
		assert(r = #v);
		for i in 1..r repeat m(i, j) := add!(m(i, j), v.i, n);
	}

	-- dot product of j-th column of m with v, which can be shorter
	local dot!(w:V F, m:M F, j:I, v:V V F):V F == {
		nv := #v;
		n := numberOfRows m;
		assert(n >= nv);
		zero! w;
		for i in 1..nv repeat w := add!(w, m(i, j), v.i);
		w;
	}

	if R has RationalRootRing then {
		kernel(L:SYS RX):M FX == {
			import from B, I;
			(hom, part) := solve!(L, zero(0, 0), true);
			assert(zero? numberOfColumns part);
			hom;
		}

		local indeq(r:A M RX, n:I):RX == {
			import from LinearAlgebra(RX, M RX);
			import from LinearOrdinaryRecurrenceEGElimination(R,_
								RX, M RX);
			TRACE("sys1pol::indeq: r = ", r);
			mat := r.0;
			(rank?, rk) := rankLowerBound mat;
			rk < n => trailingIndicialEquation(r, n);
			assert(rk = n);
			determinant mat;
		}

		degreeBound(L:SYS RX):Z == {
			import from I, M FX;
			(r, e, n, bd) := bound(L, zero(0, 0));
			bd;
		}

		-- TEMPORARY: ONLY HOMOGENEOUS SYSTEMS FOR NOW
		local bound(L:SYS RX, g:M FX):(A M RX, Z, I, Z) == {
			import from B, I, RX, Partial Z;
			import from LinearOrdinaryOperatorToRecurrence(R,_
								RX, RXY, RXE);
			TIMESTART;
			n := machine order L;
			assert(n > 0);
			(r, e) := recurrence L;
			TIME("sys1pol::bound: recurrence at ");
			TRACE("sys1pol::bound: e = ", e);
			eq := indeq(r, n);
			TRACE("sys1pol::bound: eq = ", eq);
			assert(~zero?(eq));
			b:Z := {
				failed?(u := maxIntegerRoot eq) => prev e;
				e + retract u;
			}
			TRACE("sys1pol::bound: b = ", b);
			(r, e, n, b);
		}

		-- homsols? is true if a basis of the kernel is also wanted
		-- always returns (zero(*,0), partsol) if homsols? is false
		local solve!(L:SYS RX, g:M FX, homsols?:B):(M FX, M FX) == {
			(r, e, n, bd) := bound(L, g);
			solve(r, e, n, bd, g, homsols?);
		}
	}
}
