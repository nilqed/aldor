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
------------------------- polysol.as --------------------------
#include "sumit"

#if ASDOC
\thistype{LODOPolynomialSolutions}
\History{Manuel Bronstein}{30/6/95}{created}
\History{Manuel Bronstein}{9/12/98}{added parametric right--hand side}
\Usage{import from \this(R, Rx, Rxd)}
\Params{
{\em R} & GcdDomain        & Coefficients of the polynomials\\
        & RationalRootRing & \\
{\em Rx} & UnivariatePolynomialCategory R &
Coefficients of the equations\\
{\em Rxd} & LinearOrdinaryDifferentialOperatorCategory Rx &
The differential equations\\
}
\Descr{\this(R, Rx, Rxd) provides a polynomial solver for linear ordinary
differential equations in $R[x,\frac d{dx}]$.}
\begin{exports}
polynomialKernel: & Rxd $\to$ V Rx & Compute the polynomial solutions\\
polynomialKernel: & HEQ $\to$ V Rx & Compute the polynomial solutions\\
polynomialKernel: & (Rxd, V Rx) $\to$ (V Rx, M R) &
Compute the polynomial solutions\\
polynomialKernel: & (HEQ, V Rx) $\to$ (V Rx, M R) &
Compute the polynomial solutions\\
polynomialSolution: & (Rxd, Rx) $\to$ (Rx, R) & Compute a polynomial solution\\
polynomialSolution: & (HEQ, Rx) $\to$ (Rx, R) & Compute a polynomial solution\\
\end{exports}
\begin{aswhere}
V &==& Vector\\
M &==& DenseMatrix\\
HEQ &==& HolonomicEquation(R, Rx, Rxd)\\
\end{aswhere}
#endif

macro {
	I	== SingleInteger;
	Z	== Integer;
	Q	== Quotient R;
	Qx	== DenseUnivariatePolynomial Q;
	HR	== HolonomicRecurrence(R, Rx);
	RR	== RationalRoot;
	ARR	== PrimitiveArray;
	V	== Vector;
	M	== DenseMatrix;
	EQ	== HolonomicEquation(R, Rx, Rxd);
	SING	== PlaneSingularity(R, Rx);
}

LODOPolynomialSolutions(R: Join(GcdDomain, RationalRootRing),
			Rx: UnivariatePolynomialCategory R,
			Rxd:LinearOrdinaryDifferentialOperatorCategory Rx):with{
		minimize: (V Rx, M R, I) -> (V Rx, M R);
		polynomialKernel: Rxd -> V Rx;
		polynomialKernel: EQ -> V Rx;
		polynomialKernel: (Rxd, V Rx) -> (V Rx, M R);
		polynomialKernel: (EQ, V Rx) -> (V Rx, M R);
#if ASDOC
\aspage{polynomialKernel}
\Usage{\name~L\\ \name(L, $[g_1,\dots,g_m]$)}
\Signatures{
\name: & Rxd $\to$ Vector Rx\\
\name: & HolonomicEquation(R, Rx, Rxd) $\to$ Vector Rx\\
\name: & (Rxd, Vector Rx) $\to$ (Vector Rx, DenseMatrix R)\\
\name: & (HEQ, Vector Rx) $\to$ (Vector Rx, DenseMatrix R)\\
}
\begin{aswhere}
HEQ &==& HolonomicEquation(R, Rx, Rxd)\\
\end{aswhere}
\Params{
{\em L} &              Rxd              & a differential equation\\
        & HolonomicEquation(R, Rx, Rxd) &\\
$[g_1,\dots,g_m]$ & Vector Rx & polynomials\\
}
\Retval{\name(L) returns a basis for $\Ker~L \cap R[x]$, while
\name($L, [g_1,\dots,g_m]$) returns $[h_1,\dots,h_n]$ and a matrix $M$
such that any solution of $L y = \sum_{j=1}^m c_j g_j$ must be of the
form $y = \sum_{i=1}^n y_i h_i$ where the $y_i$'s and $c_j$'s are
constants satisfying $M (y_1,\dots,y_n,c_1,\dots,c_m)^T = 0$.}
\seealso{rationalKernel(LODORationalSolutions)}
#endif
		polynomialSolution: (EQ, Rx) -> (Rx, R);
		polynomialSolution: (Rxd, Rx) -> (Rx, R);
#if ASDOC
\aspage{polynomialSolution}
\Usage{\name(L,g)}
\Signatures{
\name: & (Rxd, Rx) $\to$ (Rx, R)\\
\name: & (HolonomicEquation(R, Rx, Rxd), Rx) $\to$ (Rx, R)\\
}
\Params{
{\em L} &              Rxd              & a differential equation\\
        & HolonomicEquation(R, Rx, Rxd) &\\
{\em g} & Rx & a polynomial\\
}
\Retval{Returns $(p, r)$ with $r \ne 0$ such that $L(p/r) = g$ or $(0, 0)$ if
$L y = g$ has no solution in $Q(R)[x]$ where $Q(R)$ is the quotient field
of $R$.}
\Remarks{\name($L,0$) returns $(0,1)$ only when $L y = 0$ has no
nonzero polynomial solution.}
\seealso{rationalSolution(LODORationalSolutions)}
#endif
} == add {
	local qring?:Boolean		== R has QRing;
	local field?:Boolean		== R has SumitField;
	local coef1(p:Rx, i:Z):R	== coefficient(p, prev i);
	local deg1(p:Rx):Z		== next degree p;

	polynomialSolution(L:Rxd, g:Rx):(Rx, R) == {
		import from EQ;
		polynomialSolution(L::EQ, g);
	}

	polynomialSolution(L:EQ, g:Rx):(Rx, R) == {
		TRACE("polysol::polynomialSolution:L = ", L);
		TRACE("polysol::polynomialSolution:g = ", g);
		import from I, R, V R, List V R, M R, V Rx;
		zero? g => {
			K := polynomialKernel L;
			TRACE("polysol::polynomialSolution:K = ", K);
			#K = 0 => (0, 1);
			(K.1, 1);
		}
		vg:V Rx := zero 1;
		vg.1 := g;
		(h, m) := polynomialKernel(L, vg);
		TRACE("polysol::polynomialSolution:h = ", h);
		TRACE("polysol::polynomialSolution:m = ", m);
		(dim := #h) = 0 => (0, 0);
		d := next dim;
		for v in nullSpace m repeat {
			assert(#v = d);
			~zero?(v.d) => {
				y:Rx := 0;
				for i in 1..dim repeat y := add!(y, v.i * h.i);
				TRACE("polysol::polynomialSolution:y = ", y);
				TRACE("polysol::polynomialSolution:v.d = ",v.d);
				return (y, v.d);
			}
		}
		(0, 0);
	}

	polynomialKernel(L:Rxd):V Rx == {
		import from EQ;
		polynomialKernel(L::EQ);
	}

	polynomialKernel(L:Rxd, g:V Rx):(V Rx, M R) == {
		import from EQ;
		polynomialKernel(L::EQ, g);
	}

	local degreeBound(L:EQ):Z == {
		import from SING, Partial SING;
		failed?(u := singularityAtInfinity L) => 0;
		degreeBound retract u;
	}

	-- degree bound is the max of
	--    (i) homogeneous degree bound
	--   (ii) max(degree rhs) + order drop at infinity
	--  (iii) order of operator minus 1
	local degreeBound(L:EQ, g:V Rx):Z == {
		import from I, Rx;
		m:Z := 0;
		for i in 1..#g | ~zero?(g.i) repeat
			if (d := degree(g.i)) > m then m := d;
		zero?(n := order L) => m;
		max(degreeBound L, max(m + dropAtInfinity L, prev n));
	}

	polynomialKernel(L:EQ):V Rx == {
		import from I, R, Z, Rx, Rxd;
		(c, m) := trailingMonomial(op := operator L);
		zero? m => polKernel L;
		v := polKernel shift(op, m);
		dim := #v;
		mm:I := retract m;    -- 1, x, x^2, ..., x^{mm-1} are zeros of L
		w := zero(mm + dim);  -- 1,x,...,x^{mm-1} + integrals of others
		for i in 1..mm repeat w.i := monomial(1, prev(i)::Z);
		for i in 1..dim repeat {
			(ignore, integral) := int(v.i, mm);
			w(mm + i) := integral;
		}
		w;
	}

	polynomialKernel(L:EQ, g:V Rx):(V Rx, M R) == {
		import from I, Z, R, Rx, Rxd, V R;
		assert(#g > 0);
		#g = 1 and zero?(g.1) => {		-- homogeneous equation
			K := polynomialKernel L;
			zero?(#K)=> (zero 1,zero(1,2));	-- no nonzero solutions
			(K, zero(1, next(#K)));		-- nontrivial solutions
		}
		(c, m) := trailingMonomial(op := operator L);
		zero? m => polKernel(L, g);
		(v, mat) := polKernel(shift(op, m), g);
		(rm, cm) := dimensions mat;
		dim := #v;
		mm:I := retract m;    -- 1, x, x^2, ..., x^{mm-1} are zeros of L
		w:V Rx:=zero(mm+dim);  -- 1,x,...,x^{mm-1} + integrals of others
		for i in 1..mm repeat w.i := monomial(1, prev(i)::Z);
		wc:V R := zero cm;
		for i in 1..cm repeat wc.i := 1;
		for i in 1..dim repeat {
			-- D^m(integral) = const * v.i
			(const, integral) := int(v.i, mm);
			w(mm + i) := integral;
			wc.i := const;
		}
		-- now insert mm 0-columns in front of mat to correspond
		-- to the (arbitrary) coefficients of 1,x,...,x^{mm-1}
		-- and multiply the first dim columns of mat by wc.1,...,wc.dim
		assert(cm = dim + #g);
		bigmat := zero(rm, cm + mm);
		for i in 1..rm repeat for j in 1..cm repeat
			bigmat(i, j + mm) := wc.j * mat(i, j);
		minimize(w, bigmat, #g);
	}

	-- n = number of g's on the right-hand side
	minimize(h:V Rx, mat:M R, n:I):(V Rx, M R) == {
		import from I, R, V R, List V R;
		TRACE("polysol::minimize:h = ", h);
		TRACE("polysol::minimize:mat = ", mat);
		TRACE("polysol::minimize:n = ", n);
		empty?(K := nullSpace mat) => (zero 0, zero(0, 0));
		TRACE("polysol::minimize:K = ", K);
		(r := #K) >= (m := #h) => (h, nonzero mat);
		assert(n + m = cols mat);
		a := zero(n + m, r + n);
		w:V Rx := zero r;
		for v in K for j in 1@I.. repeat {
			dotprod:Rx := 0;
			for i in 1..m repeat {
				a(i,j) := v.i;
				dotprod := add!(dotprod, v.i * h.i);
			}
			w.j := dotprod;
		}
		for j in 1..n for i in next(m).. repeat a(i, r + j) := 1;
		TRACE("polysol::minimize:a = ", a);
		(w, nonzero(mat * a));
	}

	-- returns the number nonzero rows of mat and their indices
	local nonzerorows(mat:M R):(I, ARR I) == {
		n:I := 0;
		(r, c) := dimensions mat;
		a := new(r, 0);
		for i in 1..r repeat if nonzero?(mat, i, c) then {
			n := next n;
			a.n := i;
		}
		(n, a);
	}

	local nonzero?(mat:M R, r:I, c:I):Boolean == {
		import from R;
		for j in 1..c repeat ~zero?(mat(r, j)) => return true;
		false;
	}

	-- remove all the zero rows of mat
	local nonzero(mat:M R):M R == {
		import from I, ARR I;
		TRACE("polysol::nonzero:mat = ", mat);
		(r, c) := dimensions mat;
		(n, a) := nonzerorows mat;
		TRACE("polysol::nonzero:n = ", n);
		n = r => mat;
		m := zero(n, c);
		for i in 1..n repeat for j in 1..c repeat m(i,j) := mat(a.i, j);
		TRACE("polysol::nonzero:m = ", m);
		m;
	}

	-- returns (c, q) such that D^m q = c p and c is a nonzero constant
	local int(p:Rx, m:I):(R, Rx) == {
		q:Rx := p;
		c:R := 1;
		for i in 1..m repeat {
			(d, q) := int q;
			c := times!(c, d);
		}
		(c, q);
	}

	-- returns (c, q) such that Dq = c p and c is a nonzero constant
	local int(p:Rx):(R, Rx) == {
		import from Z, R, Partial R;
		qring? => (1, qringint p);
		n := prodexp p;
		q:Rx := 0;
		for term in p repeat {
			(c, m) := term;
			m1 := next m;
			assert(~failed? exactQuotient(n * c, m1::R));
			q := add!(q, quotient(n * c, m1::R), m1);
		}
		(n, q);
	}

	-- returns c such that c p is integrable in R[x]
	local prodexp(p:Rx):R == {
		import from Z;
		n:R := 1;
		for term in p repeat {
			(c, m) := term;
			if ~zero?(c) then {
				(g, j, d) := gcdquo(next(m)::R, c);
				n := times!(n, j);
			}
		}
		n;
	}

	if R has QRing then { local qringint(p:Rx):Rx == integrate p; }

	-- returns L D^{-m}
	local shift(L:Rxd, m:Z):EQ == {
		import from Z, Rxd;
		Lm:Rxd := 0;
		for term in L repeat {
			(c, n) := term;
			assert(n >= m);
			Lm := add!(Lm, c, n - m);
		}
		Lm::EQ;
	}

	-- this code is for operators whose coefficient of D^0 is nonzero
	local polKernel(L:EQ, g:V Rx):(V Rx, M R) == {
		import from I, Z, Rxd;
		N := degreeBound(L, g);
		assert(N >= 0);
		TRACE("polynomialKernel::degree bound = ", N);
		-- TEMPORARY: SHOULD ALSO USE SERIES METHOD LATER
		undeterminedCoeffs(operator L, retract N, g);
	}

	-- this code is for operators whose coefficient of D^0 is nonzero
	local polKernel(L:EQ):V Rx == {
		import from I, Z, Rxd;
		zero? degree(op := operator L) => zero 0;
		N := degreeBound L;
		assert(N >= 0);
		TRACE("polynomialKernel::polKernel:degree bound = ", N);
		A := recurrenceDegree op;
		TRACE("polynomialKernel::polKernel:A = ", A);
		-- undet coeffs uses N^3
		-- series uses (A + #sing) (min(degree(L), A) + #sing)^2
		m := min(degree op, A);
		TRACE("polynomialKernel:polKernel:m = ", m);
		-- TEMPORARY THIS CUTOFF IGNORES THE NUMBER OF SINGULARITIES
		N^3 <= A * m^2 => undeterminedCoeffs(op, retract N);
		seriesMethod(op, retract N);
	}

	-- parametric right-hand-side case, rhs = c1 g.1 + ... + cs g.s
	local undeterminedCoeffs(L:Rxd, N:I, g:V Rx):(V Rx, M R) == {
		import from Z, R, Partial R, Rx, Array Rx;
		import from LinearMapToMatrix(R, Rx, M R);
		START__TIME;
		assert(N >= 0);
		TRACE("polysol::undeterminedCoeffs:L = ", L);
		TRACE("polysol::undeterminedCoeffs:N = ", N);
		TRACE("polysol::undeterminedCoeffs:g = ", g);
		basis:Array Rx := new(N1 := next N, 0);
		for i in 0..N repeat basis(next i) := monomial(1, i::Z);
		TRACE("polysol::undeterminedCoeffs::basis = ", basis);
		-- mL is such that L(p) corresponds to mL*p wrt basis
		mL := matrix((p:Rx):Rx +-> L p, basis, coef1, deg1);
		TRACE("polysol::undeterminedCoeffs:mL = ", mL);
		-- mg is such that its column i are the coeffs of g.i wrt basis
		arr:Array Rx := new(ng := #g, 0);
		for i in 1..ng repeat arr.i := g.i;
		mg := matrix(arr, coef1, deg1);
		TRACE("polysol::undeterminedCoeffs:mg = ", mg);
		TIME("polysol::undeterminedCoeffs:matrices at ");
		-- The solutions are all the pairs (y,c) such that mL*y = mg*c
		rL := rows mL;
		assert(N1 = cols mL);
		rg := rows mg;
		assert(ng = cols mg);
		-- build the matrix [mL, -mg] corresponding to mL*y = mg*c
		conds := zero(max(rL, rg), N1 + ng);
		for i in 1..rL repeat
			for j in 1..N1 repeat conds(i, j) := mL(i, j);
		for j in 1..ng for k in next N1.. repeat
			for i in 1..rg repeat conds(i, k) := - mg(i, j);
		vec := zero N1;
		for i in 1..N1 repeat vec.i := basis.i;
		TIME("polysol::undeterminedCoeffs:unminimized solutions at ");
		minimize(vec, conds, ng);
	}

	-- homogeneous case
	local undeterminedCoeffs(L:Rxd, N:I):V Rx == {
		import from Z, R, Partial R, Rx, Array Rx, List V R;
		import from LinearMapToMatrix(R, Rx, M R);
		START__TIME;
		assert(N >= 0);
		TRACE("polysol::undeterminedCoeffs:L = ", L);
		TRACE("polysol::undeterminedCoeffs:N = ", N);
		basis:Array Rx := new(next N, 0);
		for i in 0..N repeat basis(next i) := monomial(1, i::Z);
		TRACE("polysol::undeterminedCoeffs:basis = ", basis);
		kern :=
		   undeterminedCoefficients((p:Rx):Rx +-> L p,basis,coef1,deg1);
		TIME("polysol::undeterminedCoeffs:nullspace at ");
		TRACE("polysol::undeterminedCoeffs:kernel = ", kern);
		dim := #kern;
		TRACE("polysol:undeterminedCoeffs:dimension = ", dim);
		sols:V Rx := zero dim;
		zero? dim => sols;
		for i in 1..dim repeat {
			sols.i := 0;
			lci := lcoeff(kerni := first kern, N);
			ilci := {
				failed?(u := reciprocal lci) => 0@R;
				retract u;
			}
			monic? := ~zero? ilci;
			kern := rest kern;
			for j in N..0 by -1 repeat {
				c := kerni(next j);
				if monic? then c := ilci * c;
				sols.i := add!(sols.i, c, j::Z);
			}
			if ~monic? then sols.i := primitivePart(sols.i);
		}
		TIME("polysol::undeterminedCoeffs:solutions at ");
		sols;
	}

	local lcoeff(v:V R, N:I):R == {
		for i in next N .. 1 by -1 repeat ~zero?(v.i) => return(v.i);
		0;
	}

	local seriesMethod(L:Rxd, N:I):V Rx == {
		import from Z, HR,
		    LinearOrdinaryDifferentialOperatorToDifferenceOperator(R,_
									Rx,Rxd);
		START__TIME;
		r := recurrence L;
		TIME("series method, recurrence at ");
		TRACE("polysol::series method:recurrence = ", r);
		d:I := retract degree L;
		field? => polKernel(r, N, d);
		qpolKernel(r, N, d);
	}

	local qpolKernel(r:HR, n:I, nu:I):V Rx == {
		import from V Qx, SeriesSolutionsQuotient(R, Rx, Qx);
		import from UnivariateFreeAlgebraOverQuotient(R, Rx, Q, Qx);
		K := polynomialKernel(r, n, nu);
		v:V Rx := zero(dim := #K);
		for i in 1..dim repeat {
			(c, p) := makeIntegral(K.i);
			v.i := p;
		}
		v;
	}

	if R has SumitField then {
		local polKernel(r:HR, n:I, nu:I):V Rx == {
			import from SeriesSolutions(R pretend SumitField, Rx);
			polynomialKernel(r, n, nu);
		}
	}

	local recurrenceDegree(L:Rxd):Z == {
		import from Rx;
		p := leadingCoefficient L;
		(c, e) := trailingMonomial p;
		a := degree L - e;
		b := degree L - degree p;
		for term in reductum L repeat {
			(p, n) := term;
			(c, e) := trailingMonomial p;
			m := n - e;
			if m > a then a := m;
			m := n - degree p;
			if m < b then b := m;
		}
		assert(a >= b);
		a - b;
	}
}
