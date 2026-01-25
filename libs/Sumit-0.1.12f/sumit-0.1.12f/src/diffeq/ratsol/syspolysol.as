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
------------------------- syspolysol.as --------------------------
-- Copyright Manuel Bronstein, 1998
-- Copyright INRIA, 1998

#include "sumit"

#if ASDOC
\thistype{LODSPolynomialSolutions}
\History{Manuel Bronstein}{28/4/98}{created}
\Usage{import from \this(R, Rx)}
\Params{
{\em R} & GcdDomain        & Coefficients of the polynomials\\
        & RationalRootRing & \\
{\em Rx} & UnivariatePolynomialCategory R &
Coefficients of the equations\\
}
\Descr{\this(R, Rx) provides a polynomial solver for linear ordinary
differential systems of the form $a Y' = A Y$ where $a \in R[x]$ and
$A$ is a matrix with coefficients in $R[x]$.}
\begin{exports}
polynomialKernel & SYS Rx $\to$ Matrix Rx & Compute the polynomial solutions\\
polynomialKernel & SYS Quotient Rx $\to$ Matrix Rx
& Compute the polynomial solutions\\
\end{exports}
\begin{aswhere}
SYS &==& LinearOrdinaryDifferentialSystem\\
\end{aswhere}
#endif

macro {
	I	== SingleInteger;
	Z	== Integer;
	RR	== RationalRoot;
	Q	== Quotient R;
	Qx	== DenseUnivariatePolynomial Q;
	RF	== Quotient Rx;
	HRS	== FirstOrderHolonomicRecurrenceSystem(R, Rx);
	ARR	== PrimitiveArray;
	V	== Vector;
	MAT	== DenseMatrix;
	SYS	== LinearOrdinaryDifferentialSystem;
	Rxe	== LinearOrdinaryDifferenceOperator(R, Rx);
}

LODSPolynomialSolutions(R: Join(GcdDomain, RationalRootRing),
			Rx: UnivariatePolynomialCategory R): with {
		determiningMatrix: (SYS Rx, V Z, Bits) -> MAT R;
		determiningMatrix: (SYS RF, V Z, Bits) -> MAT R;
		polynomialKernel: SYS Rx -> MAT Rx;
		polynomialKernel: (SYS Rx, Z) -> MAT Rx;
		polynomialKernel: (SYS RF, Z) -> MAT Rx;
		polynomialKernel: (SYS Rx, V Z) -> MAT Rx;
		polynomialKernel: (SYS RF, V Z) -> MAT Rx;
		polynomialKernel: (SYS Rx, V Z, Bits) -> MAT Rx;
		polynomialKernel: (SYS RF, V Z, Bits) -> MAT Rx;
#if ASDOC
\aspage{polynomialKernel}
\Usage{\name~L}
\Signatures{
\name: & LinearOrdinaryDifferentialSystem Rx $\to$ Matrix Rx\\
\name: & LinearOrdinaryDifferentialSystem RX $\to$ Matrix Rx\\
}
\Params{
{\em L} & LinearOrdinaryDifferentialSystem Rx & A differential system\\
        & LinearOrdinaryDifferentialSystem RF &\\
}
\Retval{Returns a basis for $\Ker~L \cap R[x]^n$
where $n$ is the dimension of $L$.}
#endif
} == add {
	local field?:Boolean == R has SumitField;

	polynomialKernel(L:SYS Rx):MAT Rx == {
		import from I, Z, ARR I, Bits;
		n := retract order L;
		seriesMethod(L, new n, true n, true);
	}

#if OLDERSTUFF
	polynomialKernel(L:SYS Rx):MAT Rx == {
		import from I, Z, Rx, RR, List RR;
		(a, A) := matrix L;
		(r, c) := dimensions A;
		first?:Boolean := true;
		-- compute the max degree of A
		local dA:Z;
		for i in 1..r repeat for j in 1..c | ~zero?(b:= A(i,j)) repeat {
			d := degree b;
			if first? or d > dA then {
				dA := d;
				first? := false;
			}
		}
		da := degree a;
		nu := da - dA;			-- order of A/a at infinity
		nu > 1 => polynomialKernel(L, 0);	-- only constant sols
		nu < 1 => error "polynomialKernel::irregular case not handled";
		ASSERT(one? nu);
		ax := monomial(leadingCoefficient a, 1);
		B:MAT Rx := zero(r, c);
		for i in 1..r repeat for j in 1..c repeat {
			b := A(i, j);
			if (~zero?(b)) and zero?(dA - degree b) then
				B(i, j) := leadingCoefficient(b)::Rx;
		}
		ASSERT(r = c);
		for i in 1..r repeat B(i, i) := B(i, i) - ax;
		zero?(p := determinant B) =>
			error "polynomialKernel::nonsimple case not handled";
		empty?(l := integerRoots p) => zero(r, 0);
		nua := integerValue first l;
		for rr in rest l repeat {
			nu := integerValue rr;
			if nu > nua then nua := nu;
		}
		nua < 0 => zero(r, 0);
		polynomialKernel(L, nua);
	}
#endif

	polynomialKernel(L:SYS Rx, N:Z):MAT Rx ==
		polynomialKernel(L, vec(order L, N));

	polynomialKernel(L:SYS RF, N:Z):MAT Rx ==
		polynomialKernel(L, vec(order L, N));

	polynomialKernel(L:SYS Rx, N:V Z):MAT Rx == {
		import from Bits;
		polynomialKernel(L, N, true(#N));
	}

	polynomialKernel(L:SYS RF, N:V Z):MAT Rx == {
		import from Bits;
		polynomialKernel(L, N, true(#N));
	}

	determiningMatrix(L:SYS Rx, N:V Z, which:Bits):MAT R ==
		seriesMethodMatrix(L, ret N, which);

	polynomialKernel(L:SYS Rx, N:V Z, which:Bits):MAT Rx ==
		seriesMethod(L, ret N, which, false);

	local ret(N:V Z):ARR I == {
		import from I, Z, ARR I;
		a:ARR I := new(n := #N);
		for i in 1..n repeat a.i := retract(N.i);
		a;
	}

	local vec(n:Z, N:Z):V Z == {
		import from I, Z, V Z;
		v := zero(m := retract n);
		for i in 1..m repeat v.i := N;
		v;
	}

	determiningMatrix(L:SYS RF, N:V Z, which:Bits):MAT R ==
		determiningMatrix(makeIntegral L, N, which);

	polynomialKernel(L:SYS RF, N:V Z, which:Bits):MAT Rx ==
		polynomialKernel(makeIntegral L, N, which);

	local makeIntegral(L:SYS RF):SYS Rx == {
		import from Rx, RF, MAT Rx,
			MatrixCategoryOverQuotient(Rx, MAT Rx, RF, MAT RF);
		(a, A) := matrix L;
		(d, B) := makeIntegral A;	-- B = d A, d a polynomial
		f := d * a;			-- the system is f Y' = B Y
		nf := numerator f;
		df := denominator f;
		if ~one? df then B := times!(df, B);
		system(nf, B);
	}

	local translate(a:Rx, m:MAT Rx):(SYS Rx, Z) == {
		import from I;
		n := ordinaryPoint a;
		x := monom + n::Rx;	-- y = x - n
		(r, c) := dimensions m;
		A := zero(r, c);
		for i in 1..r repeat for j in 1..c repeat A(i, j) := m(i, j)(x);
		(system(a x, A), n);
	}

	local seriesMethodMatrix(L:SYS Rx, N:ARR I, which:Bits):MAT R == {
		import from I, Z, R, Rx;
		(a, m) := matrix L;
		zero? coefficient(a, 0) => {
			(sys, n) := translate(a, m);
			ASSERT(~zero? n);
			seriesMethodMatrix0(sys, N, which);
		}
		seriesMethodMatrix0(L, N, which);
	}

	local seriesMethod(L:SYS Rx, N:ARR I, which:Bits,
		computeBound?:Boolean):MAT Rx == {
		import from I, Z, R, Rx;
		(a, m) := matrix L;
		zero? coefficient(a, 0) => {
			(sys, n) := translate(a, m);
			ASSERT(~zero? n);
			sol := seriesMethod0(sys, N, which, computeBound?);
			y := monom - n::Rx;
			(r, c) := dimensions sol;
			B := zero(r, c);
			for i in 1..r repeat for j in 1..c repeat
				B(i, j) := sol(i, j)(y);
			B;
		}
		seriesMethod0(L, N, which, computeBound?);
	}

	-- this code is only for systems that are nonsingular at x=0
	local seriesMethodMatrix0(L:SYS Rx, N:ARR I, which:Bits):MAT R == {
		import from Z, HRS;
		r := recurrence L;
		d:I := retract order L;
		field? => polKernelMatrix(r, N, d, which);
		qpolKernelMatrix(r, N, d, which);
	}

	-- this code is only for systems that are nonsingular at x=0
	local seriesMethod0(L:SYS Rx, N:ARR I, which:Bits,
		computeBound?:Boolean):MAT Rx == {
		import from I, Z, Partial Z, HRS;
		d:I := retract order L;
		r := recurrence L;
		if computeBound? then {
			failed?(u := degreeBound r) =>
				error "seriesMethod:cannot compute bound";
			n := retract retract u;
			for i in 1..d repeat N.i := n;
		}
		field? => polKernel(r, N, d, which);
		qpolKernel(r, N, d, which);
	}

	-- this code is only for systems that are nonsingular at x=0
	local recurrence(L:SYS Rx):HRS == {
		import from Z, R, Rx, Rxe;
		r:Rxe := 0;
		TRACE("polysol::recurrence, r = ", r);
		(a, m) := matrix L;
		ASSERT(~zero?(coefficient(a, 0)));
		d := degree a;
		n:Rx := monom;
		for term in a repeat {
			(c, e) := term;
			r := add!(r, c * (n + (1 - e)::Rx), d - e);
			TRACE("polysol::recurrence, r = ", r);
		}
		shift(r, 1 - d, m);
	}

	local qpolKernelMatrix(r:HRS, n:ARR I, nu:I, which:Bits):MAT R == {
		import from MAT Q, SeriesSolutionsQuotient(R, Rx, Qx);
		import from MatrixCategoryOverQuotient(R, MAT R, Q, MAT Q);
		makeRowIntegral determiningMatrix(r, n, nu, which);
	}

	local qpolKernel(r:HRS, n:ARR I, nu:I, which:Bits):MAT Rx == {
		import from V Rx, MAT Qx, SeriesSolutionsQuotient(R, Rx, Qx);
		K := polynomialKernel(r, n, nu, which);
		(ro, co) := dimensions K;
		v:MAT Rx := zero(ro, co);
		for j in 1..co repeat makeColIntegral!(v, K, j);
		v;
	}

	local makeColIntegral!(v:MAT Rx, m:MAT Qx, c:I):() == {
		import from R, ARR R, Rx;
		import from UnivariateFreeAlgebraOverQuotient(R, Rx, Q, Qx);
		r := rows m;
		l:R := 1;
		va:ARR R := new r;
		for i in 1..r repeat {
			(a, p) := makeIntegral m(i, c);		-- p = a m(i, c)
			va.i := a;
			v(i, c) := p;
			l := lcm(a, l);
		}
		for i in 1..r repeat
			v(i, c) := quotient(l, va.i) * v(i, c);
	}

	if R has SumitField then {
		local polKernel(r:HRS, n:ARR I, nu:I, which:Bits):MAT Rx == {
			import from SeriesSolutions(R pretend SumitField, Rx);
			polynomialKernel(r, n, nu, which);
		}

		local polKernelMatrix(r:HRS, n:ARR I, nu:I, w:Bits):MAT R == {
			import from SeriesSolutions(R pretend SumitField, Rx);
			determiningMatrix(r, n, nu, w);
		}
	}
}
