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
------------------------------ sit_lodopol.as ------------------------------
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
	M == DenseMatrix;
	RXE == LinearOrdinaryRecurrence(R, RX);
	PFX == Partial FX;
}

#if ALDOC
\thistype{LinearOrdinaryOperatorPolynomialSolutions}
\History{Manuel Bronstein}{30/6/95}{created}
\History{Manuel Bronstein}{9/12/98}{added parametric right--hand side}
\History{Manuel Bronstein}{7/6/2000}{modified to use series solver throughout}
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
\Descr{\this(R, F, $\iota$, RX, RXY, FX) provides a polynomial solver
for linear ordinary differential or recurrence operators with
polynomial coefficients.}
\begin{exports}
\asexp{kernel}: & (RXY, Z) $\to$ V FX & Polynomial solutions\\
\asexp{particularSolution}:
& (RXY, Z, FX) $\to$ \astype{Partial} FX & A polynomial solution\\
& (RXY, Z, V FX) $\to$ V FX & Some polynomial solutions\\
\asexp{solve}:
& (RXY, Z, FX) $\to$ (V FX, \astype{Partial} FX) & Polynomial solutions\\
& (RXY, Z, V FX) $\to$ (V FX, V FX) & Polynomial solutions\\
\end{exports}
\begin{exports}[if $R$ has \astype{RationalRootRing} then]
\asexp{kernel}: & RXY $\to$ V FX & Polynomial solutions\\
\asexp{parametricSolve}:
& (RXY, V FX) $\to$ (V FX, M F) & Polynomial solutions\\
\asexp{particularSolution}:
& (RXY, FX) $\to$ \astype{Partial} FX & A polynomial solution\\
& (RXY, V FX) $\to$ V FX & Some polynomial solutions\\
\asexp{solve}:
& (RXY, FX) $\to$ (V FX, \astype{Partial} FX) & Polynomial solutions\\
& (RXY, V FX) $\to$ (V FX, V FX) & Polynomial solutions\\
\end{exports}
\begin{aswhere}
M &==& \astype{DenseMatrix}\\
V &==& \astype{Vector}\\
Z &==& \astype{Integer}\\
\end{aswhere}
#endif

LinearOrdinaryOperatorPolynomialSolutions(R:IntegralDomain,
		F:Field, inj: R -> F,
		RX: UnivariatePolynomialCategory R,
		RXY:UnivariateSkewPolynomialCategory RX,
		FX: Join(CommutativeRing, UnivariateFreeFiniteAlgebra F)):with {
			kernel: (RXY, Z) -> V FX;
#if ALDOC
\aspage{kernel}
\Usage{\name~L\\ \name(L, n)}
\Signatures{
\name: & RXY $\to$ \astype{Vector} FX\\
\name: & (RXY, \astype{Integer}) $\to$ \astype{Vector} FX\\
}
\Params{
{\em L} & RXY & A linear ordinary differential or recurrence operator\\
{\em n} & \astype{Integer} & A degree bound (optional)\\
}
\Descr{\name(L) returns a basis for all the polynomial solutions of $Ly = 0$,
while \name(L,n) returns a basis for the polynomial solutions of $Ly = 0$
of degree at most $n$.}
\Remarks{\name(L) is available only if R has \astype{RationalRootRing}.
Produces an error if $L$ is neither a differential or recurrence
operator. The polynomials in the kernel are expressed in terms of
the basis $P_n$ described in
\asfunc{LinearOrdinaryOperatorToRecurrence}{recurrence}.}
#endif
			if R has RationalRootRing then {
				parametricSolve: (RXY, V FX) -> (V FX, M F);
#if ALDOC
\aspage{parametricSolve}
\Usage{\name(L, [$g_1,\dots,g_m$])}
\Signature{(RXY, \astype{Vector} FX)}
{(\astype{Vector} FX, \astype{DenseMatrix} F)}
\Params{
{\em L} & RXY & A linear ordinary differential or recurrence operator\\
$g_i$ & FX & polynomials\\
}
\Retval{Returns $h_1,\dots,h_s$ and a matrix
$A$ such that for every $\alpha_1,\dots,\alpha_s \in F$,
$$
L \paren{\sum_{i=1}^s \alpha_i h_i} = \sum_{j=1}^m \beta_j g_j
$$
where $\beta = A \alpha$. Furthermore, every solution of
$L y = \sum_{j=1}^m c_j g_j$ must be of that form.
}
\Remarks{Produces an error if $L$ is neither a differential or recurrence
operator. The polynomials $g_j$ and $h_i$ are expressed in terms of
the basis $P_n$ described in
\asfunc{LinearOrdinaryOperatorToRecurrence}{recurrence}.}
#endif
			}
			particularSolution: (RXY, Z, FX) -> PFX;
			particularSolution: (RXY, Z, V FX) -> V FX;
#if ALDOC
\aspage{particularSolution}
\Usage{\name(L, g)\\ \name(L, n, g)\\
\name(L, [$g_1,\dots,g_m$])\\ \name(L, n, [$g_1,\dots,g_m$])}
\Signatures{
\name: & (RXY, FX) $\to$ \astype{Partial} FX\\
\name: & (RXY, \astype{Integer}) $\to$ \astype{Partial} FX\\
\name: & (RXY, \astype{Vector} FX) $\to$ \astype{Vector} FX\\
\name: & (RXY, \astype{Integer}, \astype{Vector} FX) $\to$ \astype{Vector} FX\\
}
\Params{
{\em L} & RXY & A linear ordinary differential or recurrence operator\\
{\em n} & \astype{Integer} & A degree bound (optional)\\
$g, g_i$ & FX & polynomials\\
}
\Descr{\name(L, g) returns \failed if $L y = g$ has no polynomial solution,
a solution otherwise, while
\name(L, n, g) returns \failed if $L y = g$ has no polynomial solution
of degree at most $n$, such a solution otherwise.
\name(L, [$g_1,\dots,g_m$]) returns $y_1,\dots,y_m$ such that $L y_i = g_i$,
except if $y_i = 0$ and $g_i \ne 0$, in which case $L y = g_i$ has no
polynomial solution. Finally \name(L, n, [$g_1,\dots,g_m$]) returns
$y_1,\dots,y_m$ all of degree at most $n$ such that $L y_i = g_i$,
except if $y_i = 0$ and $g_i \ne 0$, in which case $L y = g_i$ has no
polynomial solution of degree at most $n$.}
\Remarks{\name(L, g) and \name(L, [$g_1,\dots,g_m$]) are available only
when the ring R has \astype{RationalRootRing}.
Produces an error if $L$ is neither a differential or recurrence
operator. The polynomials $g_j$ and $y_i$ are expressed in terms of
the basis $P_n$ described in
\asfunc{LinearOrdinaryOperatorToRecurrence}{recurrence}.
Using the version with a vector of right-hand sides is more efficient
than calling repeatedly the version with a single right-hand side.}
\seealso{\asexp{solve}}
#endif
			solve: (RXY, Z, FX) -> (V FX, PFX);
			solve: (RXY, Z, V FX) -> (V FX, V FX);
#if ALDOC
\aspage{solve}
\Usage{\name(L, g)\\ \name(L, n, g)\\
\name(L, [$g_1,\dots,g_m$])\\ \name(L, n, [$g_1,\dots,g_m$])}
\Signatures{
\name: & (RXY, FX) $\to$ \astype{Partial} FX\\
\name: & (RXY, \astype{Integer}) $\to$ \astype{Partial} FX\\
\name: & (RXY, \astype{Vector} FX) $\to$ \astype{Vector} FX\\
\name: & (RXY, \astype{Integer}, \astype{Vector} FX) $\to$ \astype{Vector} FX\\
}
\Params{
{\em L} & RXY & A linear ordinary differential or recurrence operator\\
{\em n} & \astype{Integer} & A degree bound (optional)\\
$g, g_i$ & FX & polynomials\\
}
\Descr{\name(L, g) and \name(L, [$g_1,\dots,g_m$]) return
($[y_1,\dots,y_s], \alpha)$ where $y_1,\dots,y_s$ is
a basis for all the polynomial solutions of $Ly = 0$,
and $\alpha$ is the result that \asexp{particularSolution} would return
on the same input.
\name(L, n, g) and \name(L, n, [$g_1,\dots,g_m$]) return
($[y_1,\dots,y_s], \alpha)$ where $y_1,\dots,y_s$ is
a basis for the polynomial solutions of $Ly = 0$ of degree at most $n$
and $\alpha$ is the result that \asexp{particularSolution} would return
on the same input.}
\Remarks{\name(L, g) and \name(L, [$g_1,\dots,g_m$]) are available only
if R has \astype{RationalRootRing}.
Produces an error if $L$ is neither a differential or recurrence
operator. The polynomials $g_j$ and $y_i$ are expressed in terms of
the basis $P_n$ described in
\asfunc{LinearOrdinaryOperatorToRecurrence}{recurrence}.
Using the version with a vector of right-hand sides is more efficient
than calling repeatedly the version with a single right-hand side.}
\seealso{\asexp{kernel},\asexp{particularSolution}}
#endif
			if R has RationalRootRing then {
				kernel: RXY -> V FX;
				particularSolution: (RXY, FX) -> PFX;
				particularSolution: (RXY, V FX) -> V FX;
				solve: (RXY, FX) -> (V FX, PFX);
				solve: (RXY, V FX) -> (V FX, V FX);
			}
} == add {
	kernel(L:RXY, bound:Z):V FX == {
		import from B;
		(hom, part) := solve!(L, bound, empty, true);
		assert(empty? part);
		hom;
	}

	-- if g.i <> 0 then sol.i = 0 means no particular solution exists
	-- if g.i == 0 then sol.i is automatically 0
	particularSolution(L:RXY, bound:Z, g:V FX):V FX == {
		import from B;
		(hom, part) := solve!(L, bound, copy g, false);
		assert(empty? hom);
		part;
	}

	particularSolution(L:RXY, bound:Z, g:FX):PFX == {
		import from B, I, V FX;
		zero? g => [0];
		(hom, part) := solve!(L, bound, [g], false);
		assert(empty? hom); assert(one?(#part));
		zero?(p := part.1) => failed;
		[p];
	}

	solve(L:RXY, bound:Z, g:FX):(V FX, PFX) == {
		import from B, I;
		(hom, part) := solve!(L, bound, [g], true);
		assert(one?(#part));
		zero?(p := part.1) and ~zero? g => (hom, failed);
		(hom, [p]);
	}

	solve(L:RXY, bound:Z, g:V FX):(V FX, V FX) == {
		import from B;
		solve!(L, bound, copy g, true);
	}

	-- homsols? is true if a basis of the kernel is also wanted
	-- always returns (empty, partsol) if homsols? is false
	local solve!(L:RXY, bound:Z, g:V FX, homsols?:B):(V FX, V FX) == {
		import from I, FX, PFX;
		import from UnivariateFreeFiniteAlgebra2(R, RX, F, FX);
		import from LinearOrdinaryOperatorToRecurrence(R, RX, RXY, RXE);
		TIMESTART;
		assert(~zero? L);
		nrhs := #g;
		bound < 0 => (empty, zero nrhs);
		(c, L) := primitive L;
		cc := map(inj) c;			-- content of LHS
		TIME("lodopol::solve: pp(L) at ");
		n := machine degree L;
		assert(n > 0);
		(r, e) := recurrence L;
		TIME("lodopol::solve: recurrence at ");
		-- there can be no particular solution if either
		--   (1)  c does not divide g.i, or
		--   (2)  bound < |c| + |g.i| + drop L
		-- so replace all those g.i's by 0
		-- (2) cannot happen if the bound is computed by solve below
		mu := drop L;
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 1..nrhs | ~zero?(g.i) repeat {
		i:I := 1; while i <= nrhs repeat if ~zero?(g.i) then {
			u := exactQuotient(g.i, cc);
			if failed? u then g.i := 0;
			else {
				g.i := retract u;
				if bound < degree(g.i) + mu then g.i := 0;
			}
			i := next i;
		}
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
	-- if g.i <> 0 then partsol.i = 0 means no particular solution exists
	-- if g.i == 0 then partsol.i is automatically 0
	--
	-- When g.i <> 0, we require that bound >= degree g.i + drop(operator)
	-- This ensures that the particular solution computed does not
	-- produce nonzero terms if continued as a series beyond the bound.
	-- It also ensures that constraints arising from singularities
	-- beyond the bound are automatically satisfied by the solution,
	-- hence that it is a solution even with a singular recurrence
	-- This requirement is automatically satisfied if the bound is
	-- computed by solve$%, and is tested by the other callers above
	local solve(L:RXE, e:Z, n:I, bound:Z, g:V FX, homsols?:B):(V FX,V FX)=={
		import from RX, FX, F, LinearAlgebra(F, M F);
		import from LinearOrdinaryRecurrenceTools(R, F, inj, RX, RXE);
		TIMESTART;
		nrhs := #g;
		bound < 0 => (empty, zero nrhs);
		inhom? := ~zero? g;
		-- exit if g = 0 and the homogeneous sols were not requested
		~(inhom? or homsols?) => (empty, zero nrhs);
		maxsing := machine degree leadingCoefficient L;
		sing:PrimitiveArray I := new next maxsing;
		constraints:V V F := zero maxsing;
		crhs:V V F := empty;
		if inhom? then {
			crhs := zero nrhs;
			-- TEMPORARY: LOOP-INLINING BUG 1203
			-- for i in 1..nrhs repeat crhs.i := zero maxsing;
			i:I := 1; while i <= nrhs repeat {crhs.i := zero maxsing; i := next i; }
		}
		local kh:Stream V F;
		local ki:Stream Cross(V F, V F);
		if inhom? then ki:=
			[kernel(L,e,sing,constraints,crhs,coefficients g,nrhs)];
		else kh := [kernel(L, e, sing, constraints)];
		TIME("lodopol::solve: solution stream set at ");
		m := machine(degree L - trailingDegree L);
		N := machine bound;
		-- forces all terms to be computed up to N+m
		if inhom? then (w, r) := ki(N+m); else w := kh(N+m);
		TIME("lodopol::solve: solution stream computed at ");
		nsing := sing.0;	-- number of singularities crossed
		assert(0 <= nsing); assert(nsing <= maxsing);
		sys:M F := zero(m + nsing, #w);
		local rhsys:M F;
		if inhom? then rhsys := zero(m + nsing, nrhs);
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 1..m repeat {	-- beyond degree bound ==> 0 or -rh
		i:I := 1; while i <= m repeat {
			if inhom? then {
				(v, r) := ki(N+i);
				-- TEMPORARY: LOOP-INLINING BUG 1203
				-- for j in 1..nrhs repeat rhsys(i, j) := -r.j;
				j:I:=1; while j<=nrhs repeat { rhsys(i, j) := -r.j; j := next j}
			}
			else v := kh(N+i);
			assert(#v <= #w);
			-- TEMPORARY: LOOP-INLINING BUG 1203
			-- for j in 1..#v repeat sys(i, j) := v.j;
			j:I := 1; while j<=#v repeat {sys(i, j):= v.j;j:=next j}
			i := next i;
		}
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 1..nsing repeat {	-- singular constraints
		i:I := 1; while i <= nsing repeat {
			v := constraints.i;
			assert(#v <= #w);
			mi := m + i;
			-- TEMPORARY: LOOP-INLINING BUG 1203
			-- for j in 1..#v repeat sys(mi, j) := v.j;
			j:I:=1; while j<=#v repeat {sys(mi, j) := v.j;j:=next j}
			if inhom? then {
				-- TEMPORARY: LOOP-INLINING BUG 1203
				-- for j in 1..nrhs repeat rhsys(mi,j) := crhs.j.i;
				j:I:=1; while j<=nrhs repeat {rhsys(mi,j) := crhs.j.i;j:=next j}
			}
			i := next i;
		}
		TIME("lodopol::solve: linear system set at ");
		sol:M F := zero(0, 0);
		psol?:PrimitiveArray B := new nrhs;
		psol1? := false;
		local psol:M F; local diag:V F;
		if inhom? then {
			if homsols? then (sol, psol, diag) := solve(sys, rhsys);
			    else (psol, diag) := particularSolution(sys, rhsys);
			assert(nrhs = #diag);
			-- TEMPORARY: LOOP-INLINING BUG 1203
			-- for j in 1..nrhs repeat {
			j:I:= 1; while j<=nrhs repeat {
				assert(one?(diag.j) or zero?(diag.j));
				psol?(prev j) := one?(diag.j);
				if psol?(prev j) then psol1? := true;
				j := next j;
			}
		}
		else {
			assert(homsols?);
			sol := kernel sys;
		}
		TIME("lodopol::solve: linear system solved at ");
		polker:V FX := zero(d := numberOfColumns sol);
		partsol:V FX := zero nrhs;
		-- compute the solutions by descending order of degree
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- if d > 0 or psol1? then for i in N..0 by -1 repeat {
		if d > 0 or psol1? then { i:=N; while i>=0 repeat {
			ii := i::Z;
			if inhom? then (v, r) := ki.i; else v := kh.i;
			-- TEMPORARY: LOOP-INLINING BUG 1203
			-- for j in 1..d repeat {
			j:I:= 1; while j<=d repeat {
				polker.j := add!(polker.j, dot(sol, j, v), ii);
				j := next j;
			}
			-- TEMPORARY: LOOP-INLINING BUG 1203
			-- for j in 1..nrhs | psol?(prev j) repeat {
			j:I:= 1; while j<=nrhs repeat {
				if psol?(prev j) then {
				partsol.j:=add!(partsol.j,r.j+dot(psol,j,v),ii);
				}
				j := next j;
			}
			-- TEMPORARY: LOOP-INLINING BUG 1203
			i := prev i; }
		}
		TIME("lodopol::solve: polynomial solutions at ");
		-- If e > 0, then [1,x,...,x^{e-1}] are also homogeneous sols
		homsols? and e > 0 => {
			ee := machine e;
			xpolker:V FX := zero(d + ee);
			for s in 1..ee repeat xpolker.s:=monomial(1,prev(s)::Z);
			for s in 1..d repeat xpolker(s+ee) := polker.s;
			(xpolker, partsol);
		}
		(polker, partsol);
	}

	-- returns -1 if all entries are 0
	local degree(g:V FX):Z == {
		import from B, FX;
		d:Z := -1;
		for f in g | ~zero? f repeat d := max(d, degree f);
		d;
	}

#if 0
	-- UNCLEAR WHETHER THIS WOULD WORK FOR BOUNDS TOO LOW
	parametricSolve(L:RXY, bound:Z, g:V FX):(V FX, M F) == {
		import from B, I, FX;
		import from LinearOrdinaryOperatorToRecurrence(R, RX, RXY, RXE);
		assert(~zero? L);
		nrhs := #g;
		bound < 0 => (empty, zero(0, 0));
		n := machine degree L;
		assert(n > 0);
		(r, e) := recurrence L;
		parametricSolve(r, e, n, bound, g);
	}
#endif

	local parametricSolve(L:RXE, e:Z, n:I, bound:Z, g:V FX):(V FX, M F) == {
		import from RX, FX, F, V F, LinearAlgebra(F, M F);
		import from LinearOrdinaryRecurrenceTools(R, F, inj, RX, RXE);
		TIMESTART;
		bound < 0 => (empty, zero(0, 0));
		nrhs := #g;
		maxsing := machine degree leadingCoefficient L;
		sing:PrimitiveArray I := new next maxsing;
		constraints:V V F := zero maxsing;
		crhs:V V F := zero nrhs;
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 1..nrhs repeat crhs.i := zero maxsing;
		i:I:= 1; while i<=nrhs repeat {crhs.i := zero maxsing;i:=next i}
		k:Stream Cross(V F, V F) :=
			[kernel(L,e,sing,constraints,crhs,coefficients g,nrhs)];
		TIME("lodopol::parametricSolve: solution stream set at ");
		m := machine(degree L - trailingDegree L);
		N := machine bound;
		-- forces all terms to be computed up to N+m
		(w, r) := k(N+m);
		TIME("lodopol::parametricSolve: solution stream computed at ");
		nsing := sing.0;	-- number of singularities crossed
		assert(0 <= nsing); assert(nsing <= maxsing);
		dw := #w;		-- number of homogeneous generators
		dim := dw + nrhs;	-- number of indeterminates
		sys:M F := zero(m + nsing, dim);
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 1..m repeat {		-- beyond degree bound ==> -rh
		i:I:=1; while i<=m repeat {
			(v, r) := k(N+i);
			assert(#v <= dw);
			-- TEMPORARY: LOOP-INLINING BUG 1203
			-- for j in 1..#v repeat sys(i, j) := v.j;
			j:I:= 1; while j<=#v repeat {sys(i, j) := v.j;j:=next j}
			-- TEMPORARY: LOOP-INLINING BUG 1203
			-- for j in 1..nrhs repeat sys(i, j + dw) := r.j;
			j:I:= 1; while j<=nrhs repeat {sys(i, j + dw) := r.j;j:=next j}
			i := next i;
		}
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in 1..nsing repeat {	-- singular constraints
		i:I:=1; while i<=nsing repeat {
			v := constraints.i;
			assert(#v <= dw);
			mi := m + i;
			-- TEMPORARY: LOOP-INLINING BUG 1203
			-- for j in 1..#v repeat sys(mi, j) := v.j;
			j:I:= 1; while j<=#v repeat {sys(mi,j) := v.j;j:=next j}
			-- TEMPORARY: LOOP-INLINING BUG 1203
			-- for j in 1..nrhs repeat sys(mi, j+dw) := - crhs.j.i;
			j:I:= 1; while j<=nrhs repeat {sys(mi,j+dw) := - crhs.j.i;j:=next j}
			i := next i;
		}
		TIME("lodopol::parametricSolve: linear system set at ");
		-- At this point, op(y) = \sum_j c_j g_j if and only if
		-- y = \sum_i d_i y_i + \sum_j c_j p_j  and sys (d,c)^T = 0
		-- where y_i = poly given by v.i up to N
		--       p_j = poly given by r.j up to N
		sol := kernel sys;
		zero?(d := numberOfColumns sol) => (empty, zero(0, 0));
		kergen:V FX := zero d;
		-- compute the solution generators by descending order of degree
		-- TEMPORARY: LOOP-INLINING BUG 1203
		-- for i in N..0 by -1 repeat {
		i:=N; while i>=0 repeat {
			ii := i::Z;
			(v, r) := k.i;
			-- TEMPORARY: LOOP-INLINING BUG 1203
			-- for j in 1..d repeat {
			j:I := 1; while j<=d repeat {
				kergen.j := add!(kergen.j, dot(sol,j,v,r), ii);
				j := next j;
			}
			i := prev i;
		}
		TIME("lodopol::parametricSolve: solution generators at ");
		(kergen, sol(next dw, 1, nrhs, d));
	}

	-- dot product of j-th column of m with v, which can be shorter
	local dot(m:M F, j:I, v:V F):F == dot(m, j, v, empty);

	-- dot product of j-th column of m with [v|w], which can be shorter
	local dot(m:M F, j:I, v:V F, w:V F):F == {
		nv := #v;
		n := numberOfRows m;
		assert(n >= nv + #w);
		x:F := 0;
		for i in 1..nv repeat x := add!(x, m(i, j) * v.i);
		for i in 1..#w repeat x := add!(x, m(i + nv, j) * w.i);
		x;
	}

	if R has RationalRootRing then {
		kernel(L:RXY):V FX == {
			import from B;
			(hom, part) := solve!(L, empty, true);
			assert(empty? part);
			hom;
		}

		-- if g.i <> 0 then sol.i=0 means no particular solution exists
		-- if g.i == 0 then sol.i is automatically 0
		particularSolution(L:RXY, g:V FX):V FX == {
			import from B;
			(hom, part) := solve!(L, copy g, false);
			assert(empty? hom);
			part;
		}

		particularSolution(L:RXY, g:FX):PFX == {
			import from B, I, V FX;
			zero? g => [0];
			(hom, part) := solve!(L, [g], false);
			assert(empty? hom); assert(one?(#part));
			zero?(p := part.1) => failed;
			[p];
		}

		solve(L:RXY, g:FX):(V FX, PFX) == {
			import from B, I;
			(hom, part) := solve!(L, [g], true);
			assert(one?(#part));
			zero?(p := part.1) and ~zero? g => (hom, failed);
			(hom, [p]);
		}

		-- simultaneous solving of several right-hand-sides
		solve(L:RXY, g:V FX):(V FX, V FX) == {
			import from B;
			solve!(L, copy g, true);
		}

		local bound(L:RXY, g:V FX):(RXE, Z, I, Z) == {
			import from B, I, Z, Partial Z, RX, RXE,
			       LinearOrdinaryOperatorToRecurrence(R,RX,RXY,RXE);
			TIMESTART;
			assert(~zero? L);
			n := machine degree L;
			assert(n > 0);
			(r, e) := recurrence L;
			TIME("lodopol::bound: recurrence at ");
			(p, m) := trailingMonomial r;
			b := m + e;
			bd := b + degree g;		-- bd=b-1 if g=[0,...,0]
			if ~failed?(u := maxIntegerRoot p) then
						bd := max(bd, b + retract u);
			TIME("lodopol::bound: bound at ");
			(r, e, n, bd);
		}

		local solve!(L:RXY, g:V FX, homsols?:B):(V FX, V FX) == {
			import from I, FX, PFX;
			import from UnivariateFreeFiniteAlgebra2(R, RX, F, FX);
			(c, L) := primitive L;
			cc := map(inj) c;		-- content of LHS
			for i in 1..#g | ~zero?(g.i) repeat {
				u := exactQuotient(g.i, cc);
				g.i := { failed? u => 0; retract u }
			}
			(r, e, n, bd) := bound(L, g);
			solve(r, e, n, bd, g, homsols?);
		}

		parametricSolve(L:RXY, g:V FX):(V FX, M F) == {
			(r, e, n, bd) := bound(L, g);
			parametricSolve(r, e, n, bd, g);
		}
	}
}
