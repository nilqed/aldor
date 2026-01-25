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
------------------------- sysratsol.as --------------------------
#include "sumit"

#if ASDOC
\thistype{LODSRationalSolutions}
\History{Manuel Bronstein}{8/5/97}{created}
\Usage{import from \this(R, Rx)}
\Params{
{\em R} & GcdDomain        & Coefficients of the polynomials\\
        & RationalRootRing & \\
{\em Rx} & UnivariatePolynomialCategory R &
Coefficients of the differential systems\\
}
\Descr{\this(R, Rx) provides a rational function solver for linear ordinary
differential systems of the form $a Y' = A Y$ where $a \in R[x]$ and
$A$ is a matrix with coefficients in $R[x]$.}
\begin{exports}
endomorphisms & SYS Rx $\to$ List M & Basis of the endormorphism ring\\
endomorphisms & SYS Quotient Rx $\to$ List M & Basis of the endormorphism ring\\
rationalKernel & SYS Rx $\to$ M & Compute all the rational solutions\\
rationalKernel & (SYS Rx, Rx) $\to$ M & Compute some rational solutions\\
rationalKernel & SYS Quotient Rx $\to$ M & Compute all the rational solutions\\
rationalKernel & (SYS Quotient Rx, Rx) $\to$ M &
Compute some rational solutions\\
\end{exports}
\begin{aswhere}
M &==& DenseMatrix Quotient Rx\\
SYS &==& LinearOrdinaryDifferentialSystem\\
\end{aswhere}
#endif

macro {
	ARR	== PrimitiveArray;
	I	== SingleInteger;
	Z	== Integer;
	PI	== Product;
	RF	== Quotient Rx;
	V	== Vector;
	M	== DenseMatrix;
	SYS	== LinearOrdinaryDifferentialSystem;
	LODO	== LinearOrdinaryDifferentialOperator;
}

LODSRationalSolutions(R: Join(GcdDomain, RationalRootRing),
			Rx: UnivariatePolynomialCategory R): with {
		determiningMatrix: (SYS Rx, V Rx, V Z, Bits) -> M R;
		determiningMatrix: (SYS RF, V Rx, V Z, Bits) -> M R;
		endomorphisms: SYS Rx -> List M RF;
		endomorphisms: SYS RF -> List M RF;
#if ASDOC
\aspage{endomorphisms}
\Usage{\name~L}
\Signatures{
\name:& SYS Rx $\to$ List DenseMatrix Quotient Rx\\
\name: & SYS Quotient Rx $\to$ List DenseMatrix Quotient Rx\\
}
\begin{aswhere}
SYS &==& LinearOrdinaryDifferentialSystem\\
\end{aswhere}
\Params{
{\em L} & LinearOrdinaryDifferentialSystem Rx & A differential system\\
        & LinearOrdinaryDifferentialSystem RF &\\
}
\Retval{Returns a basis for the space
$$
\mbox{End}_G(\mbox{Sol}(L)) = \{ Z \in RF^{n,n} \st Z' = A Z - Z A\}
$$
where $L$ is of the form $Y' = A Y$.}
\Remarks{The current implementation uses the cyclic vector method.}
\seealso{eigenring{Eigenring}}
#endif
		rationalKernel: SYS Rx -> M RF;
		rationalKernel: (SYS Rx, Rx) -> M RF;
		rationalKernel: SYS RF -> M RF;
		rationalKernel: (SYS RF, Rx) -> M RF;
		rationalKernel: (SYS Rx, V Rx, Z) -> M RF;
		rationalKernel: (SYS RF, V Rx, Z) -> M RF;
		rationalKernel: (SYS Rx, V Rx, V Z) -> M RF;
		rationalKernel: (SYS RF, V Rx, V Z) -> M RF;
		rationalKernel: (SYS Rx, V Rx, V Z, Bits) -> M RF;
		rationalKernel: (SYS RF, V Rx, V Z, Bits) -> M RF;
#if ASDOC
\aspage{rationalKernel}
\Usage{\name~L\\ \name(L, p)}
\Signatures{
\name: & SYS Rx $\to$ DenseMatrix Quotient Rx\\
\name: & SYS Quotient Rx $\to$ DenseMatrix Quotient Rx\\
\name: & (SYS Rx, Rx) $\to$ DenseMatrix Quotient Rx\\
\name: & (SYS Quotient Rx, Rx) $\to$ DenseMatrix Quotient Rx\\
}
\begin{aswhere}
SYS &==& LinearOrdinaryDifferentialSystem\\
\end{aswhere}
\Params{
{\em L} & LinearOrdinaryDifferentialSystem Rx & A differential system\\
        & LinearOrdinaryDifferentialSystem RF &\\
{\em p} & Rx & A polynomial\\
}
\Retval{\name~L returns a matrix whose columns form a basis for
$\Ker~L \cap R(x)^n$, while \name($L,p$) returns a matrix whose columns form
a basis for its subspace of solutions of the form $y = a(x)/b(x)$ where
the roots of $b(x)$ are among the roots of $p(x)$.}
\Remarks{The current implementation uses the cyclic vector method.}
#endif
} == add {
	rationalKernel(s:SYS RF):M RF	== ratKernel(s, singularities s);
	rationalKernel(s:SYS Rx):M RF	== ratKernel(s, singularities s);

	local matrices(m:M RF, n:Z):List M RF == {
		import from I;
		[matrix(m, i, n) for i in 1..cols m];
	}

	local vec(n:Z, N:Z):V Z == {
		import from I;
		a:V Z := zero(m := retract n);
		for i in 1..m repeat a.i := N;
		a;
	}

	rationalKernel(s:SYS RF, denoms: V Rx, bound:Z):M RF ==
		rationalKernel(s, denoms, vec(order s, bound));

	rationalKernel(s:SYS Rx, denoms: V Rx, bound:Z):M RF ==
		rationalKernel(s, denoms, vec(order s, bound));

	rationalKernel(s:SYS RF, denoms: V Rx, bound:V Z):M RF == {
		import from Bits;
		rationalKernel(s, denoms, bound, true(#bound));
	}

	rationalKernel(s:SYS Rx, denoms: V Rx, bound:V Z):M RF == {
		import from Bits;
		rationalKernel(s, denoms, bound, true(#bound));
	}

	determiningMatrix(s:SYS RF, denoms: V Rx, bound:V Z, w:Bits):M R == {
		(a, A) := matrix s;
		determiningMatrix(a, A, denoms, bound, w);
	}

	determiningMatrix(s:SYS Rx, denoms: V Rx, bound:V Z, w:Bits):M R == {
		import from RF, MatrixCategoryOverQuotient(Rx, M Rx, RF, M RF);
		(a, A) := matrix s;
		determiningMatrix(1, inv(a::RF) * A, denoms, bound, w);
	}

	rationalKernel(s:SYS RF, denoms: V Rx, bound:V Z, which:Bits):M RF == {
		(a, A) := matrix s;
		rationalKernel(a, A, denoms, bound, which);
	}

	rationalKernel(s:SYS Rx, denoms: V Rx, bound:V Z, which:Bits):M RF == {
		import from RF, MatrixCategoryOverQuotient(Rx, M Rx, RF, M RF);
		(a, A) := matrix s;
		rationalKernel(1, inv(a::RF) * A, denoms, bound, which);
	}

	local rationalKernel(a:RF, A:M RF, den:V Rx, bd:V Z, w:Bits):M RF == {
		import from I, M Rx, RF, LODSPolynomialSolutions(R, Rx);
		TRACE("sysratsol::rationalKernel, a = ", a);
		TRACE("sysratsol::rationalKernel, A = ", A);
		TRACE("sysratsol::rationalKernel, den = ", den);
		TRACE("sysratsol::rationalKernel, bd = ", bd);
#if ASTRACE
		print << "sysratsol::rationalKernel, w = ";
		for i in 1..#den repeat print << w.i << " ";
		print << newline;
#endif
		L := shift!(bd, a, A, den);
		sol := polynomialKernel(L, bd, w);
		TRACE("sysratsol::rationalKernel, sol = ", sol);
		(m, dim) := dimensions sol;
		TRACE("sysratsol::rationalKernel, kernel dimension = ", dim);
		Y:M RF := zero(m, dim);
		for i in 1..m | w.i repeat for j in 1..dim repeat
			Y(i, j) := sol(i, j) / den.i;
		TRACE("sysratsol::rationalKernel, Y = ", Y);
		Y;
	}

	-- side-effects bd
	local shift!(bd:V Z, a:RF, A:M RF, den:V Rx):SYS RF == {
		import from I, Z, Rx, RF, M Rx;
		(n, m) := dimensions A;
		ASSERT(n = m); ASSERT(n = #den);
		B:M RF := zero(n, n);
		for i in 1..n repeat {
			d := den.i;
			ASSERT(~zero? d);
			bd.i := bd.i + degree d;
			B(i, i) := A(i, i) + differentiate(d) / d;
			for j in 1..n | i ~= j repeat
				B(i, j) := A(i, j) * (d / den.j);
		}
		TRACE("sysratsol::rationalKernel, B = ", B);
		TRACE("sysratsol::rationalKernel, bd = ", bd);
		system(a, B);
	}

	local determiningMatrix(a:RF, A:M RF, den:V Rx, bd:V Z, w:Bits):M R == {
		import from LODSPolynomialSolutions(R, Rx);
		L := shift!(bd, a, A, den);
		determiningMatrix(L, bd, w);
	}

	rationalKernel(s:SYS RF, sing:Rx):M RF ==
		ratKernel(s, gcd(sing, singularities s));

	rationalKernel(s:SYS Rx, sing:Rx):M RF ==
		ratKernel(s, gcd(sing, singularities s));

	endomorphisms(s:SYS Rx):List M RF ==
		matrices(rationalKernel eigenTensor s, order s);

	endomorphisms(s:SYS RF):List M RF ==
		matrices(rationalKernel eigenTensor s, order s);

	local matrix(m:M RF, col:I, nn:Z):M RF == {
		n:I := retract nn;
		a := zero(n, n);
		for i in 1..n repeat
			for j in 1..n repeat
				a(i, j) := m(i + n * prev j, col);
		a;
	}

	local ratKernel(s:SYS Rx, sing:Rx):M RF == {
		import from RF, LODO Rx,
			System2LinearOrdinaryDifferentialOperator(Rx, LODO Rx),
			MatrixCategoryOverQuotient(Rx, M Rx, RF, M RF);
		START__TIME;
		(L, U, a) := cyclicVector s;
		TIME("rationalKernel::cyclic vector at ");
		La := adjoint L;
		TIME("rationalKernel::integral adjoint at ");
		extra := extraSingularities(U, sing, leadingCoefficient L);
		TIME("rationalKernel::extra singularities at ");
		makeRational(U) * solutions(La, extra, sing, order s, L, a::RF);
	}

	local ratKernel(s:SYS RF, sing:Rx):M RF == {
		import from LODO Rx,
			System2LinearOrdinaryDifferentialOperator(RF, LODO RF),
		       UnivariateFreeAlgebraOverQuotient(Rx,LODO Rx,RF,LODO RF);
		START__TIME;
		(L, U, a) := cyclicVector s;
		TIME("rationalKernel::cyclic vector at ");
		(c, LL) := makeIntegral L;
		TIME("rationalKernel::integral cyclic vector at ");
		Ladj := adjoint LL;
		TIME("rationalKernel::adjoint at ");
		extra := extraSingularities(U, sing, leadingCoefficient LL);
		TIME("rationalKernel::extra singularities at ");
		U * solutions(Ladj, extra, sing, order s, LL, a);
	}

	local solutions(La:LODO Rx,e:Product Rx,s:Rx,n:Z,L:LODO Rx,a:RF):M RF=={
		import from I, V RF, LODORationalSolutions(R, Rx, LODO Rx),
			LinearOrdinaryDifferentialOperatorTools(Rx, LODO Rx);
		START__TIME;
		(LRx, alpha) := twist(La, e);
		LRx := primitivePart LRx;
		TIME("solutions::twisted adjoint at ");
		K := rationalKernel(LRx, s);
		TIME("solutions::scalar kernel at ");
		sol:M RF := zero(nn := retract n, dim := #K);
		d := inv(expand(e)::RF);
		apow:V RF := zero nn;		-- [1, a, a^2,..., a^(n-1)]
		apow.1 := 1;
		for i in 2..nn repeat apow.i := a * apow(prev i);
		aprime := differentiate a;
		for j in 1..dim repeat
			computeSolution!(sol, j, d * K.j, L, a, apow, aprime);
		TIME("solutions::cyclic basis kernel at ");
		sol;
	}

	local computeSolution!(sol:M RF, j:I, z:RF, L:LODO Rx,
						a:RF, apow:V RF, ap:RF):() == {
		import from Z;
		n := rows sol;
		ASSERT(#apow = n);
		sol(n, j) := leadingCoefficient(L) * z / apow.n;
		for i in prev n..1 by -1 repeat {
			sol(i, j) := coefficient(L, i::Z) * z / apow.i
					- a * differentiate(sol(next i, j))
					- i::Z * ap * sol(next i, j);
		}
	}

	local extraSingularities(P:M Rx, sing:Rx, a:Rx):Product Rx == {
		(c, det) := squareFree determinant P;
		extraSingularities(det, sing, a);
	}

	local extraSingularities(P:M RF, sing:Rx, a:Rx):Product Rx == {
		import from RF;
		(c, det) := squareFree numerator determinant P;
		extraSingularities(det, sing, a);
	}

	local extraSingularities(det:Product Rx, sing:Rx, a:Rx):Product Rx == {
		import from Z;
		(c, lc) := squareFree a;
		xtra:Product Rx := 1;
		for trm in det repeat {
			(p, n) := trm;
			(g, extra, dummy) := gcdquo(p, sing);
			if degree(extra) > 0 then {
				xtra0 := extraSingularities(extra, lc, n);
				xtra := xtra * xtra0;
			}
		}
		xtra;
	}

	local extraSingularities(p:Rx, lc:Product Rx, n:Z):Product Rx == {
		xtra:Product Rx := 1;
		for trm in lc repeat {
			(q, m) := trm;
			g := gcd(p, q);
			if degree(g) > 0 then xtra := xtra * term(g, n + m);
		}
		xtra;
	}

	local singularities(sys:SYS Rx):Rx == {
		(a, m) := matrix sys;
		squareFreePart a;
	}

	local singularities(sys:SYS RF):Rx == {
		import from I, Z, RF, M RF;
		(a, m) := matrix sys;
		p := squareFreePart numerator a;
		for i in 1..rows m repeat
			for j in 1..cols m repeat
				p := lcm(p, squareFreePart denominator m(i, j));
		ASSERT(zero? degree gcd(p, differentiate p));
		p;
	}
}

#if SUMITTEST
---------------------- test sysratsol.as --------------------------
#include "sumittest"

macro {
	I == SingleInteger;
	Z == Integer;
	ZX == DenseUnivariatePolynomial(Z, "x");
	Zx == Quotient ZX;
	M == DenseMatrix;
	SYS == LinearOrdinaryDifferentialSystem;
}


local qkernel():Boolean == {
	import from I, Z, ZX, Zx, M Zx, SYS Zx, LODSRationalSolutions(Z, ZX);
	A := zero(2, 2);
	x := monom;
	A(1,1) := A(2,2) := x::Zx;
	A(2,1) := (x^2 - x^4)::Zx;
	A(1,2) := - inv((x^2)::Zx);
	K := rationalKernel system(1, A);
	cols K ~= 1 => false;
	AK := A * K;
	differentiate(K(1,1)) = AK(1,1) and differentiate(K(2,1)) = AK(2,1);
}

local zkernel():Boolean == {
	import from I, Z, ZX, M ZX, Zx, M Zx, SYS ZX;
	import from LODSRationalSolutions(Z, ZX);
	import from MatrixCategoryOverQuotient(ZX, M ZX, Zx, M Zx);
	A:M ZX := zero(2, 2);
	x := monom;
	A(1,1) := A(2,2) := x^3;
	A(2,1) := x^4 - x^6;
	A(1,2) := - 1;
	K := rationalKernel system(x^2, A);
	cols K ~= 1 => false;
	AK := makeRational(A) * K;
	x^2 * differentiate(K(1,1)) = AK(1,1) and
		x^2 * differentiate(K(2,1)) = AK(2,1);
}

print << "Testing rational solutions of Y' = A Y..." << newline;
sumitTest("2nd order over polys", zkernel);
sumitTest("2nd order over fractions", qkernel);
print << newline;
#endif
