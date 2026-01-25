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
------------------------- series.as --------------------------
-- Copyright Manuel Bronstein, 1997-1998
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1997
-- Copyright INRIA, 1998

#include "sumit"

#if ASDOC
\thistype{SeriesSolutions}
\History{Manuel Bronstein}{5/9/97}{created}
\Usage{import from \this(R, Rx)}
\Params{
{\em R} & SumitField & Coefficients of the polynomials\\
{\em Rx} & UnivariatePolynomialCategory R & Coefficients of the equations\\
}
\Descr{\this(R, Rx) provides a series solver for linear
equations and systems with coefficients in $R[x]$.}
\begin{exports}
polynomialKernel & (RXE, SingleInteger, Integer) $\to$ Vector Rx
& Polynomial solutions\\
polynomialKernel & (SYS, SingleInteger, Integer) $\to$ DenseMatrix Rx
& Polynomial solutions\\
polynomialKernel & (SYS, ARR, Integer) $\to$ DenseMatrix Rx
& Polynomial solutions\\
polynomialKernel & (SYS, ARR, Integer, Bits) $\to$ DenseMatrix Rx
& Polynomial solutions\\
\end{exports}
\begin{aswhere}
ARR &==& PrimitiveArray SingleInteger\\
RXE &==& LinearOrdinaryDifferenceOperator(R, Rx)\\
\end{aswhere}
#endif

macro {
	I	== SingleInteger;
	Z	== Integer;
	ARR	== PrimitiveArray;
	V	== Vector;
	MAT	== DenseMatrix;
	Q	== Quotient R;
	HR	== HolonomicRecurrence(R, Rx);
	HRS	== FirstOrderHolonomicRecurrenceSystem(R, Rx);
}

SeriesSolutions(R:SumitField, Rx: UnivariatePolynomialCategory R): with {
		determiningMatrix: (HRS, ARR I, I, Bits) -> MAT R;
		polynomialKernel: (HR, I, I) -> V Rx;
		polynomialKernel: (HRS, I, I) -> MAT Rx;
		polynomialKernel: (HRS, ARR I, I) -> MAT Rx;
		polynomialKernel: (HRS, ARR I, I, Bits) -> MAT Rx;
#if ASDOC
\aspage{polynomialKernel}
\Usage{\name(L, n, $\nu$)\\ \name(S, n, $\nu$)\\
\name(S, $[n_1,\dots,n_k], \nu$)\\
\name(S, $[n_1,\dots,n_k], \nu, [b_1,\dots,b_k]$)}
\Signatures{
\name: & (REC, SingleInteger, Integer) $\to$ Vector Rx\\
\name: & (SYS, SingleInteger, Integer)
$\to$ DenseMatrix Rx\\
\name: & (SYS, Primitive Array SingleInteger, Integer) $\to$ DenseMatrix Rx\\
\name:
& (SYS, Primitive Array SingleInteger, Integer, Bits) $\to$ DenseMatrix Rx\\
}
\Params{
{\em L} & HolonomicRecurrence(R, Rx) & The recurrence\\
{\em S} & SYS & The recurrence system\\
$n,n_i$ & SingleInteger & The degree bounds\\
$\nu$ & SingleInteger & Order of the corresponding differential operator\\
$b_i$ & Bits & A bit-mask\\
}
\begin{aswhere}
REC &==& HolonomicRecurrence(R, Rx)\\
SYS &==& FirstOrderHolonomicRecurrenceSystem(R, Rx)\\
\end{aswhere}
\Descr{
\name~returns a basis for the polynomial solutions of degree at most $n$
of the differential operator or system corresponding to the given recurrence
or system. If an array of degree bounds are given, then $n_i$ is a degree
bound for the $\sth{i}$ entry of the solution vector. If a bit-mask is given,
then only the entries of the solution vector corresponding to bits that are
set are computed. In that case, the returned vectors do not necessarily
correspond to complete polynomial solutions, but any polynomial solution is
in their span.
}
#endif
} == add {
	local cross(v:V R, a:ARR ARR R, da:I, b:ARR ARR R, db:I, j:I):R == {
		ASSERT(#v = da + db);
		c:R := 0;
		for k in 1..da repeat c := add!(c, v.k * a.k.j);
		for k in 1..db repeat c := add!(c, v(da + k) * b.k.j);
		c;
	}

	-- rec is the real recurrence for (a0,a1,...)
	-- N is the degree bound on the polynomials
	-- nu is the order of the corresponding differential operator
	-- THIS ALGORITHM ASSUMES THAT THE COEFFICIENT OF D^0
	-- IN THE DIFFERENTIAL OPERATOR IS NONZERO. THIS IS ENSURED
	-- BY THE CALLING CODE (polysol.as)
	polynomialKernel(rec:HR, N:I, nu:I):V Rx == {
		import from Z, List I, List V R, ARR R, ARR ARR R, MAT R, Rx;
		TRACE("polynomialKernel::recurrence = ", rec);
		TRACE("polynomialKernel::degree bound = ", N);
		TRACE("polynomialKernel::operator order = ", nu);
		START__TIME;
		nurec:I := retract degree rec;
		TRACE("polynomialKernel::true recurrence order = ", nurec);
		M := min(nurec, nu);
		TRACE("polynomialKernel::non-singular dimension = ", M);
		a:ARR ARR R := new M;
		fill := fill! rec;
		-- compute the series with unit vectors as starting point
		a.1 := new(N + 1 + nurec, 0);
		a.1.1 := 1;
		sing := fill(a.1, M, N + nurec, true);
		TRACE("polynomialKernel::sing = ", sing);
		-- TRACE("a[*] = ", a.1);
		for i in 2..M repeat {
			a.i := new(N + 1 + nurec, 0);
			a.i.i := 1;
			fill(a.i, M, N + nurec, false);
			-- TRACE("a[*] = ", a.i);
		}
		-- compute the series corresponding to singularities
		b:ARR ARR R := new(nsing := #sing);
		for i in 1..nsing for n in sing repeat {
			b.i := new(N + 1 + nurec, 0);
			b.i.(n + 1) := 1;
			fill(b.i, n + 1, N + nurec, false);
			-- TRACE("b[*] = ", b.i);
		}
		TIME("polynomialKernel: coefficient vectors at ");
		m:MAT R := zero(nurec + nsing, M + nsing);
		for i in 1..nurec repeat {
			for j in 1..M repeat m(i, j) := a.j.(1 + N + i);
			for j in 1..nsing repeat m(i, j + M) := b.j.(1 + N + i);
		}
		red := reductum rec;
		for i in 1..nsing for n in sing repeat {
			for j in 1..M repeat m(i + nurec, j) := red(a.j, n);
			for j in 1..nsing repeat m(i+nurec, j+M) := red(b.j, n);
		}
		TRACE("m = ", m);
		TIME("polynomialKernel: matrix created at ");
		kern := nullSpace m;
		TIME("polynomialKernel: nullspace at ");
		TRACE("polynomialKernel::kernel = ", kern);
		d := #kern;
		TRACE("polynomialKernel::kernel dimension = ", d);
		sols:V Rx := zero d;
		zero? d => sols;
		-- compute the terms in descending order
		for l in N..0 by -1 repeat {
			for k in 1..d repeat {
				c := cross(kern k, a, M, b, nsing, next l);
				sols.k := add!(sols.k, c, l::Z);
			}
		}
		TIME("polynomialKernel: solutions at ");
		sols;
	}

	local trace(msg:String, a:ARR MAT R, n:I):() == {
#if ASTRACE
		import from StandardIO, MAT R;
		err := writer stderr;
		err << msg << newline;
		for i in 1..n repeat err << a.i << newline;
		err << newline;
#endif
	}

	-- rec is the real recurrence for (v0,v1,...)
	-- N is the degree bound on the polynomials
	-- nu is the order of the corresponding differential operator
	polynomialKernel(rec:HRS, N:I, nu:I):MAT Rx == {
		import from ARR I;
		ASSERT(nu > 0);
		a:ARR I := new nu;
		for i in 1..nu repeat a.i := N;
		polynomialKernel(rec, a, nu);
	}

	local max(N:ARR I, n:I, which:Bits):I == {
		ASSERT(n > 0); ASSERT(dimension(which, n) > 0);
		m:I := 0;
		first?:Boolean := true;
		for i in 1..n | which.i repeat
			if first? or m < N.i then { m := N.i; first? := false; }
		m;
	}

	polynomialKernel(rec:HRS, N:ARR I, nu:I):MAT Rx == {
		import from Bits;
		polynomialKernel(rec, N, nu, true nu);
	}

	-- rec is the real recurrence for (v0,v1,...)
	-- N is an array of degree bounds on the polynomials
	-- nu is the order of the corresponding differential operator
	-- bits tells for which unknowns to solve
	determiningMatrix(rec:HRS, N:ARR I, nu:I, which:Bits):MAT R == {
		(m, Nmax, a) := deterMatrix(rec, N, nu, which);
		m;
	}

	-- rec is the real recurrence for (v0,v1,...)
	-- N is an array of degree bounds on the polynomials
	-- nu is the order of the corresponding differential operator
	-- bits tells for which unknowns to solve
	local deterMatrix(rec:HRS,N:ARR I,nu:I,w:Bits):(MAT R,I,ARR MAT R) == {
		import from Z, Rx;
		ASSERT(nu > 0);
		-- TRACE("polynomialKernel::recurrence = ", rec);
		-- TRACE("polynomialKernel::recurrence matrix = ", matrix rec);
		-- TRACE("polynomialKernel::degree bound = ", N);
		TRACE("polynomialKernel::operator order = ", nu);
		Nmax := max(N, nu, w);
		TRACE("polynomialKernel::max degree bound = ", Nmax);
		zero?(dim := dimension(w, nu)) => (zero(nu, 0), Nmax, new 0);
		TRACE("polynomialKernel::number of rows to solve = ", dim);
		M:I := retract degree rec;
		TRACE("polynomialKernel::true recurrence order = ", M);
		-- compute the series with identity matrix as starting point
		a:ARR MAT R := new(Nmax + 1 + M);
		a.1 := one nu;
		-- fill row i from 1 to N.i + M
		fill := fill!(rec, N, M);
		fill(a, 1, Nmax + M);
		-- trace("polynomialKernel::a[*] = ", a, Nmax + M + 1);
		-- TRACE("polynomialKernel::a[*] = ", a);
		-- only select the equations (rows) such that w.i is true
		-- there are dim such rows, each provides M equations
		m:MAT R := zero(dim * M, nu);
		r:I := 1;
		for i in 1..nu | w.i repeat {
			for j in 1..M repeat {
				for k in 1..nu repeat
					m(r, k) := a(1 + N.i + j)(i, k);
				r := next r;
			}
		}
		ASSERT(r = dim * M);
		-- TRACE("m = ", m);
		(m, Nmax, a);
	}

	-- rec is the real recurrence for (v0,v1,...)
	-- N is an array of degree bounds on the polynomials
	-- nu is the order of the corresponding differential operator
	-- bits tells for which unknowns to solve
	polynomialKernel(rec:HRS, N:ARR I, nu:I, which:Bits):MAT Rx == {
		START__TIME;
		import from Z, V R, List V R, MAT R, ARR MAT R, Rx;
		(m, Nmax, a) := deterMatrix(rec,N, nu, which);
		TIME("polynomialKernel: determining matrix created at ");
		kern := nullSpace m;
		TIME("polynomialKernel: nullspace at ");
		-- TRACE("polynomialKernel::kernel = ", kern);
		d := #kern;
		TRACE("polynomialKernel::kernel dimension = ", d);
		sols:MAT Rx := zero(nu, d);
		zero? d => sols;
		-- compute the terms in descending order
		for l in Nmax..0 by -1 repeat {
			for k in 1..d repeat {
				c := a(l + 1) * kern k;
				for i in 1..nu | which.i repeat
					sols(i,k) := add!(sols(i,k), c.i, l::Z);
			}
		}
		TIME("polynomialKernel: solutions at ");
		sols;
	}
}

SeriesSolutionsQuotient(R:GcdDomain, Rx: UnivariatePolynomialCategory R,
			Qx: UnivariatePolynomialCategory Q): with {
		determiningMatrix: (HRS, ARR I, I, Bits) -> MAT Q;
		polynomialKernel: (HR, I, I) -> V Qx;
		polynomialKernel: (HRS, I, I) -> MAT Qx;
		polynomialKernel: (HRS, ARR I, I) -> MAT Qx;
		polynomialKernel: (HRS, ARR I, I, Bits) -> MAT Qx;
} == add  {
	polynomialKernel(r:HR, N:I, nu:I):V Qx == {
		import from SeriesSolutions(Q, Qx);
		polynomialKernel(qrec r, N, nu);
	}

	polynomialKernel(r:HRS, N:ARR I, nu:I):MAT Qx == {
		import from SeriesSolutions(Q, Qx);
		polynomialKernel(qrec r, N, nu);
	}

	polynomialKernel(r:HRS, N:ARR I, nu:I, which:Bits):MAT Qx == {
		import from SeriesSolutions(Q, Qx);
		polynomialKernel(qrec r, N, nu, which);
	}

	polynomialKernel(r:HRS, N:I, nu:I):MAT Qx == {
		import from SeriesSolutions(Q, Qx);
		polynomialKernel(qrec r, N, nu);
	}

	determiningMatrix(r:HRS, N:ARR I, nu:I, which:Bits):MAT Q == {
		import from SeriesSolutions(Q, Qx);
		determiningMatrix(qrec r, N, nu, which);
	}

	local qrec(r:HR):HolonomicRecurrence(Q, Qx) == {
		import from LinearOrdinaryDifferenceOperator(R, Rx);
		import from LinearOrdinaryDifferenceOperator(Q, Qx);
		import from UnivariateFreeAlgebraOverQuotient(R, Rx, Q, Qx);
		L:LinearOrdinaryDifferenceOperator(Q, Qx) := 0;
		for term in operator r repeat {
			(p, e) := term;
			L := add!(L, makeRational p, e);
		}
		shift(L, trailingDegree r);
	}

	local qrec(r:HRS):FirstOrderHolonomicRecurrenceSystem(Q, Qx) == {
		import from LinearOrdinaryDifferenceOperator(R, Rx);
		import from LinearOrdinaryDifferenceOperator(Q, Qx);
		import from UnivariateFreeAlgebraOverQuotient(R, Rx, Q, Qx);
		L:LinearOrdinaryDifferenceOperator(Q, Qx) := 0;
		for term in operator r repeat {
			(p, e) := term;
			L := add!(L, makeRational p, e);
		}
		shift(L, trailingDegree r, makeRational matrix r);
	}

	local makeRational(m:MAT Rx):MAT Qx == {
		import from I, UnivariateFreeAlgebraOverQuotient(R, Rx, Q, Qx);
		(r, c) := dimensions m;
		mm:MAT(Qx) := zero(r, c);
		for i in 1..r repeat
			for j in 1..c repeat
				mm(i, j) := makeRational m(i, j);
		mm;
	}
}
