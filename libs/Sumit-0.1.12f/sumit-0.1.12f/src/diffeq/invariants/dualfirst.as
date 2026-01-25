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
------------------------- dualfirst.as --------------------------
-- Copyright Manuel Bronstein, 1998
-- Copyright INRIA, 1998

#include "sumit"

macro {
	I	== SingleInteger;
	Z	== Integer;
	Q	== Quotient R;
	RF	== Quotient Rx;
	V	== Vector;
	M	== DenseMatrix;
	ARR	== PrimitiveArray;
	EQ	== HolonomicEquation(R, Rx, Rxd);
	SING	== PlaneSingularity(R, Rx);
	SYS	== LinearOrdinaryDifferentialSystem;
}

-- m = order of the operator
-- n = symmetric power to compute
DualFirstIntegralTools(R:IntegralDomain, Rx: UnivariatePolynomialCategory R,
	n:I, m:I): with {
		-- return an array of bits b1...bd s.t b.i is true if the degree
		-- of the corresponding monomial in Ym is d
		degree: I -> Bits;
		dimension:I;
		eval: (S:Ring, Array S) -> I -> S;
		-- fill!(A,[a0,...,a_{m-1}],i) fills the rows of A corresponding
		-- to monomials of degree i in Ym, where L = D^m + sum ai D^i
		fill!: (M RF, ARR RF, I, Derivation RF) -> ();
		multinomial: I -> Z;
		-- value(i) returns then index of Y_i^n
		value: I -> I;
		weight: I -> I;
	} == add {
	macro PP == DenseHomogeneousPowerProduct(n, m);
	import from PP;

	dimension:I		== { import from Z; retract(#$PP); }
	value(i:I):I		== index monomial i;
	weight(i:I):I		== weight lookup i;
	multinomial(i:I):Z	== multinomial lookup i;

	eval(S:Ring, a:Array S):I -> S == {
		ev := eval(S, a)$PP;
		(i:I):S +-> ev lookup i;
	}

	degree(d:I):Bits == {
		w := false dimension;
		for i in 1..dimension repeat {
			y := lookup i;
			if degree(y, m) = d then w.i := true;
		}
		w;
	}

	fill!(A:M RF, a:ARR RF, i:I, diff:Derivation RF):() == {
		for j in 1..dimension repeat {
			y := lookup j;
			if degree(y, m) = i then fill!(A, j, i, y, a, diff);
		}
	}

	-- fills the row r, corresponding to the monomial y, of degree e in Ym
	local fill!(A:M RF, r:I, e:I, y:PP, a:ARR RF, df:Derivation RF):() == {
		import from Z, RF;
		assert(e > 0); assert(degree(y, m) = e);
		e1 := prev(e)::Z;
		m1 := prev m;
		c := cols A;
		z := incdec(y, m1, m);
		kk := k := index z;
		for j in 1..c repeat A(r, j) := df A(k, j);
		for i in 1..prev m1 | (d := degree(y, i)) > 0 repeat {
			k := index incdec(z, next i, i);
			ei := d::Z;
			for j in 1..c repeat
				A(r, j) := A(r, j) - ei * A(k, j);
		}
		if e1 > 0 then {
			for i in 1..m1 repeat {
				k := index incdec(z, i, m);
				alpha := a.i;		-- coeff of D^{i-1} in L
				for j in 1..c repeat
					A(r, j) := A(r,j) + e1 * alpha * A(k,j);
			}
			alpha := a.m;
			for j in 1..c repeat
				A(r, j) := A(r, j) + e1 * alpha * A(kk, j);
		}
		if (d := degree(y, m1)) > 0 then {
			alpha := inv(next(d)::RF);
			for j in 1..c repeat A(r, j) := alpha * A(r, j);
		}
	}
}

#if ASDOC
\thistype{DualFirstIntegral}
\History{Manuel Bronstein}{22/5/98}{created}
\Usage{import from \this(R, Rx, Rxd)}
\Params{
{\em R} & GcdDomain        & Coefficients of the polynomials\\
        & RationalRootRing & \\
{\em Rx} & UnivariatePolynomialCategory R &
Coefficients of the differential operators\\
{\em Rxd} & LODO Rx & The differential operators\\
}
\begin{aswhere}
LODO &==& LinearOrdinaryDifferentialOperatorCategory\\
\end{aswhere}
\Descr{\this(R, Rx, Rxd) computes dual first integrals for
differential equations.}
\begin{exports}
dualFirstIntegral & (Rxd, Integer) $\to$ DenseMatrix Quotient Rx &
Dual first integrals\\
invariants & (Rxd, Integer) $\to$ DenseMatrix R & Invariants\\
\end{exports}
#endif

DualFirstIntegral(R: Join(GcdDomain, RationalRootRing),
		Rx: UnivariatePolynomialCategory R,
		Rxd: LinearOrdinaryDifferentialOperatorCategory Rx): with {
			determiningMatrix: (Rxd, Z) -> M R;
			dualFirstIntegral: (Rxd, Z) -> M RF;
			dualFirstIntegral: (EQ, Z) -> M RF;
#if ASDOC
\aspage{dualFirstIntegral}
\Usage{\name(L, n)}
\Signatures{
\name:& (Rx, Integer) $\to$ DenseMatrix Quotient Rx\\
\name:& (HolonomicEquation(R, Rx, Rxd), Integer) $\to$ DenseMatrix Quotient Rx\\
}
\Params{
{\em L} & Rxd & A differential equation\\
        & HolonomicEquation(R, Rx, Rxd) & \\
{\em n} & Integer & A positive integer\\
}
\Retval{
Returns a matrix whose columns form a basis for the space of solutions of
$$
Y' = Sym(A,n) Y
$$
where $A$ is the companion matrix of $L$ and $Sym(A,n)$ is the matrix
of the $\sth{n}$ symmetric power of $Y' = A Y$.
}
\Remarks{The current implementation uses the cyclic vector method if $L$ has
exponents that are not rational numbers, a direct method otherwise.}
\seealso{invariants(\this)}
#endif
			symmetricKernel: (Rxd, Z) -> V RF;
			symmetricKernel: (EQ, Z) -> V RF;
#if ASDOC
\aspage{symmetricKernel}
\Usage{\name(L, n)}
\Signatures{
\name: & (Rxd, Integer) $\to$ Vector Quotient Rx\\
\name: & (HolonomicEquation(R, Rx, Rxd), Integer) $\to$ Vector Quotient Rx\\
}
\Params{
{\em L} & Rxd & A differential equation\\
        & HolonomicEquation(R, Rx, Rxd) & \\
{\em n} & Integer & A positive integer\\
}
\Retval{\name~L returns a basis for $\Ker~\sympow{L}{n} \cap R(x)$,
where $\sympow{L}{n}$ is the \Th{n} symmetric power of $L$.
}
\Remarks{Using \name~can be more efficient than computing the symmetric
power and its kernel separately. This is the case in the current implementation
if all the exponents of $L$ are rational numbers.}
\seealso{exteriorKernel(LODORationalSolutions),\\
rationalKernel(LODORationalSolutions),\\
symmetricPower(LinearOrdinaryDifferentialOperatorCategory)}
#endif
} == add {
	symmetricKernel(L:Rxd, m:Z):V RF == {
		import from EQ;
		symmetricKernel(L::EQ, m);
	}

	dualFirstIntegral(L:Rxd, m:Z):M RF == {
		import from EQ;
		dualFirstIntegral(L::EQ, m);
	}

	determiningMatrix(L:Rxd, m:Z):M R == {
		import from EQ, LODSRationalSolutions(R, Rx);
		allRationalExponents?(eq := L::EQ) =>
			determiningMatrix dualFirst(eq, m, true);
		-- TEMPORARY
		error "determiningMatrix: equation has non-rational exponent";
	}

	dualFirstIntegral(L:EQ, m:Z):M RF == {
		import from RF, Rxd, SYS Rx, LODSRationalSolutions(R, Rx);
		import from System2LinearOrdinaryDifferentialOperator(Rx, Rxd);
		START__TIME;
		assert(m > 0);
		TRACE("dualfirst::dualFirstIntegral: L = ", L);
		TRACE("dualfirst::dualFirstIntegral: m = ", m);
		allRationalExponents? L => {
			(sys, den, bd, w) := dualFirst(L, m, false);
			-- this computes only partial candidate solutions
			k := rationalKernel(sys, den, bd, w);
			TIME("dualfirst::dualFirstIntegral: basic entries at ");
			pow:I := retract m;
			ord:I := retract order L;
			df:Derivation RF := lift(derivation$Rxd);
			-- now complete them to full candidate solutions
			f! := fill!(operator L, ord, pow, df);
			for i in 1..pow repeat f!(k, i);
			TIME("dualfirst::dualFirstIntegral: all entries at ");
			-- at this point any dual first integral is
			-- a linear combination of the columns of k with
			-- constant coefficients, verify which work
			(a, A) := matrix sys;
			k := verify(k, a, A, df);
			TIME("dualfirst::dualFirstIntegral: verified at ");
			k;
		}
		TRACE("dualfirst::dualFirstIntegral: ", "using cyclic vectors");
		s:SYS Rx := symmetricPower(operator L, m);
		rationalKernel(s, leadingCoefficient operator L);
	}

	-- returns a basis for the subspace of the col-span of Y
	-- that verify a Y' = A Y
	-- that subspace is isomorphic to the kernel of (a Y' - A Y)
	local verify(Y:M RF, a:Rx, A:M Rx, df:Derivation RF):M RF == {
		import from I, RF, V RF, List V RF;
		import from MatrixCategoryOverQuotient(Rx, M Rx, RF, M RF);
		TRACE("dualfirst::verify: Y = ", Y);
		TRACE("dualfirst::verify: a = ", a);
		TRACE("dualfirst::verify: A = ", A);
		zero? cols Y => Y;
		aa := a::RF;
		B := makeRational A;
		m := aa * map!(function df, copy Y) - B * Y;
		k := nullSpace m;
		TRACE("dualfirst::verify: k = ", k);
		Z:M RF := zero(r := rows Y, #k);
		d:I := 1;
		for sol in k repeat {
			assert(d <= #k);
			v := Y * sol;
			assert(#v = r);
			for i in 1..r repeat Z(i, d) := v.i;
			d := next d;
		}
		TRACE("dualfirst::verify: Z = ", Z);
		Z;
	}

	-- m = order of the operator
	-- n = symmetric power to compute
	-- fills the rows of A corresponding to Y_m^i
	-- assuming that all the rows corresponding to Y_m^j for j < i are done
	local fill!(L:Rxd, m:I, n:I, df:Derivation RF):(M RF, I) -> () == {
		import from Z, RF, ARR RF;
		import from DualFirstIntegralTools(R, Rx, n, m);
		a:ARR RF := new m;
		c := leadingCoefficient L;
		for i in 1..m repeat a.i := coefficient(L, prev(i)::Z) / c;
		(A:M RF, i:I):() +-> fill!(A, a, i, df);
	}

	local dualFirst(L:EQ, m:Z, all?:Boolean):(SYS Rx, V Rx, V Z, Bits) == {
		import from I,System2LinearOrdinaryDifferentialOperator(Rx,Rxd);
		assert(m > 0);
		pow:I := retract m;
		ord:I := retract order L;
		(v, b) := denoms(L, ord, pow);
		s:SYS Rx := symmetricPower(operator L, m);
		(s, v, b, which(ord, pow, all?));
	}

	-- m = order of the operator
	-- n = symmetric power to compute
	local which(m:I, n:I, all?:Boolean):Bits == {
		import from DualFirstIntegralTools(R, Rx, n, m);
		all? => true dimension;
		degree 0;
	}

	-- m = order of the operator
	-- n = symmetric power to compute
	-- This code should not be used for 2nd order operators (inefficient)
	-- returns:
	--     arrays of denominators
	--     bounds on the corresponding polynomial parts
	local denoms(eq:EQ, m:I, n:I):(V Rx, V Z) == {
		import from Z, ARR Z, Partial Z, Rx;
		import from SING, List SING, Partial SING;
		import from DualFirstIntegralTools(R, Rx, n, m);
		assert(n > 0); assert(m > 1);
		assert(allRationalExponents? eq);
		TRACE("dualfirst::denoms: eq = ", eq);
		TRACE("dualfirst::denoms: m = ", m);
		TRACE("dualfirst::denoms: n = ", n);
		dim := dimension;
		TRACE("dualfirst::denoms: dim = ", dim);
		exps:ARR Z := new dim;
		dens:V Rx := zero dim;
		for i in 1..dim repeat {
			exps.i := weight(i)::Z;
			dens.i := 1;
		}
		N := n::Z;
		for s in finiteSingularities eq repeat {
			u := minIntegerExponent(s, N);
			if ~(failed? u) then {
				p := center s;
				e := - retract u;
				for i in 1..dim repeat {
					a := e + exps.i;
					if a > 0 then
						dens.i := times!(dens.i, p^a);
				}
			}
		}
		TRACE("dualfirst::denoms: dens = ", dens);
		inf:V Z := zero dim;
		if (~failed?(v := singularityAtInfinity eq))
			and (e := degreeBound(retract v, N)) > 0 then {
				TRACE("dualfirst::denoms: degree bound = ", e);
				for i in 1..dim repeat {
					a := e - exps.i;
					if a > 0 then inf.i := a;
				}
		}
		TRACE("dualfirst::denoms: inf = ", inf);
		(dens, inf);
	}

	-- cyclic vector method
	local symKernel(L:EQ, n:Z):V RF == {
		import from Rx, Rxd, BalancedFactorization(R, Rx);
		import from LODORationalSolutions(R, Rx, Rxd);
		assert(n >= 1);
		one? n => rationalKernel L;
		op := operator L;
		rationalKernel(symmetricPower(op, n),
			balancedFactor(leadingCoefficient op, coefficients op));
	}

	symmetricKernel(L:EQ, m:Z):V RF == {
		import from I, M RF;
		assert(m > 0);
		TRACE("dualfirst::symmetricKernel: L = ", L);
		TRACE("dualfirst::symmetricKernel: m = ", m);
		order(L) <= 2 or (~allRationalExponents? L) => symKernel(L, m);
		k := dualFirstIntegral(L, m);
		pow:I := retract m;
		ord:I := retract order L;
		n := value(ord, pow);
		assert(n > 0); assert(n <= rows k);
		span nonzero(k, n);
	}

	-- m = order of the operator
	-- n = symmetric power to compute
	local value(m:I, n:I):I == {
		import from DualFirstIntegralTools(R, Rx, n, m);
		value 1;
	}

	local span(w:V RF):V RF == {
		import from I, Z, ARR I, M R, Rx,V Rx,VectorOverQuotient(Rx,RF);
		zero?(d := #w) => w;
		(a, v) := makeIntegral w;
		n := next maxdeg v;
		m:M R := zero(n, d);
		for i in 1..n repeat for j in 1..d repeat
			m(i, j) := coefficient(v.j, prev(i)::Z);
		(r, c) := span m;
		basis:V RF := zero r;
		for i in 1..r repeat basis.i := w(c.i);
		basis;
	}

	local maxdeg(v:V Rx):I == {
		import from Z, Rx;
		m:Z := 0;
		for i in 1..#v repeat {
			d := degree(v.i);
			if d > m then m := d;
		}
		retract m;
	}

	-- returns the nonzero elements of the n-th row of m
	local nonzero(m:M RF, n:I):V RF == {
		import from RF;
		t:I := 0;
		c := cols m;
		for i in 1..c repeat if ~zero?(m(n, i)) then t := next t;
		v := zero t;
		t := 1;
		for i in 1..c repeat if ~zero?(m(n, i)) then {
			v.t := m(n, i);
			t := next t;
		}
		v;
	}
}
