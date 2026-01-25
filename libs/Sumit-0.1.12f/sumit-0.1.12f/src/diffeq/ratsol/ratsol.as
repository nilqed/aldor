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
------------------------- ratsol.as --------------------------
-- Copyright Manuel Bronstein, 1995-1998
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1995-1997
-- Copyright INRIA, 1998

#include "sumit"

#if ASDOC
\thistype{LODORationalSolutions}
\History{Manuel Bronstein}{30/6/95}{created}
\History{Manuel Bronstein}{14/12/98}{added parametric right--hand side}
\Usage{import from \this(R, Rx, Rxd)}
\Params{
{\em R} & GcdDomain        & Coefficients of the polynomials\\
        & RationalRootRing & \\
{\em Rx} & UnivariatePolynomialCategory R &
Coefficients of the operators\\
{\em Rxd} & LinearOrdinaryDifferentialOperatorCategory Rx &
The differential operators\\
}
\Descr{\this(R, Rx, Rxd) provides a rational function solver for linear ordinary
differential equations in $R[x,\frac d{dx}]$.}
\begin{exports}
exteriorKernel: & (Rxd, Integer) $\to$ V Qx &
Rational solutions of an exterior power\\
rationalKernel: & Rxd $\to$ V Qx & Compute all the rational solutions\\
rationalKernel: & HEQ $\to$ V Qx & Compute all the rational solutions\\
rationalKernel:
& (Rxd, V Qx) $\to$ (V Qx, M R) & Compute all the rational solutions\\
rationalKernel:
& (HEQ, V Qx) $\to$ (V Qx, M R) & Compute all the rational solutions\\
rationalKernel: & (Rxd, Rx) $\to$ V Qx & Compute some rational solutions\\
rationalKernel: & (HEQ, Rx) $\to$ V Qx & Compute some rational solutions\\
rationalKernel:
& (Rxd, Product Rx) $\to$ V Qx & Compute some rational solutions\\
rationalKernel:
& (HEQ, Product Rx) $\to$ V Qx & Compute some rational solutions\\
rationalSolution: & (Rxd, Qx) $\to$ Partial Qx & Compute a rational solution\\
rationalSolution: & (HEQ, Qx) $\to$ Partial Qx & Compute a rational solution\\
\end{exports}
\begin{aswhere}
V &==& Vector\\
M &==& DenseMatrix\\
Qx &==& Quotient Rx\\
HEQ &==& HolonomicEquation(R, Rx, Rxd)\\
\end{aswhere}
#endif

macro {
	I	== SingleInteger;
	Z	== Integer;
	RF	== Quotient Rx;
	V	== Vector;
	M	== DenseMatrix;
	PI	== Product;
	EQ	== HolonomicEquation(R, Rx, Rxd);
	SING	== PlaneSingularity(R, Rx);
}

LODORationalSolutions(R: Join(GcdDomain, RationalRootRing),
			Rx: UnivariatePolynomialCategory R,
			Rxd:LinearOrdinaryDifferentialOperatorCategory Rx):with{
		exponentialDenom: EQ -> PI Rx;
		exteriorKernel: (Rxd, Z) -> V RF;
#if ASDOC
\aspage{exteriorKernel}
\Usage{\name(L, n)}
\Signature{(Rxd, Integer)}{Vector Quotient Rx}
\Params{
{\em L} & Rxd & A differential equation\\
{\em n} & Integer & The exterior power to consider\\
}
\Retval{\name~L returns a basis for $\Ker~\extpow{L}{n} \cap R(x)$,
where $\extpow{L}{n}$ is the \Th{n} exterior power of $L$.
}
\Remarks{Using \name~can be more efficient than computing the exterior
power and its kernel separately.}
\seealso{rationalKernel(\this),\\
symmetricPower(LinearOrdinaryDifferentialOperatorCategory)}
#endif
		rationalKernel: Rxd -> V RF;
		rationalKernel: EQ -> V RF;
		rationalKernel: (Rxd, V RF) -> (V RF, M R);
		rationalKernel: (EQ, V RF) -> (V RF, M R);
		rationalKernel: (Rxd, Rx) -> V RF;
		rationalKernel: (EQ, Rx) -> V RF;
		rationalKernel: (Rxd, PI Rx) -> V RF;
		rationalKernel: (EQ, PI Rx) -> V RF;
#if ASDOC
\aspage{rationalKernel}
\Usage{\name~L \\ \name(L, p)\\ \name(L,$\Pi$)\\ \name((L, $[g_1,\dots,g_m]$)}
\Signatures{
\name: & Rxd $\to$ Vector Quotient Rx\\
\name: & HEQ $\to$ Vector Quotient Rx\\
\name: & (Rxd, Vector Quotient Rx) $\to$ (Vector Quotient Rx, DenseMatrix R)\\
\name: & (HEQ, Vector Quotient Rx) $\to$ (Vector Quotient Rx, DenseMatrix R)\\
\name: & (Rxd, Rx) $\to$ Vector Quotient Rx\\
\name: & (HEQ, Rx) $\to$ Vector Quotient Rx\\
\name: & (Rxd, Product Rx) $\to$ Vector Quotient Rx\\
\name: & (HEQ, Product Rx) $\to$ Vector Quotient Rx\\
}
\begin{aswhere}
HEQ &==& HolonomicEquation(R, Rx, Rxd)\\
\end{aswhere}
\Params{
{\em L} & Rxd & A differential equation\\
       & HolonomicEquation(R, Rx, Rxd) &\\
{\em p} & Rx & A polynomial\\
{\em $\Pi$} & Product Rx & A product of polynomials\\
$[g_1,\dots,g_m]$ & Vector Quotient Rx & fractions\\
}
\Retval{\name~L returns a basis for $\Ker~L \cap R(x)$, while
\name($L, p$) and\\
\name($L, \prod_i p_i^{e_i}$) return a basis for the space
of all solutions of $L y = 0$ of the form $y = a(x)/b(x)$ where the roots
of $b(x)$ are among the roots of $p(x)$ or $\prod_i p_i(x)$, and\\
\name($L, [g_1,\dots,g_m]$) returns $[h_1,\dots,h_n]$ and a matrix $M$
such that any solution of $L y = \sum_{j=1}^m c_j g_j$ must be of the
form $y = \sum_{i=1}^n y_i h_i$ where the $y_i$'s and $c_j$'s are
constants satisfying $M (y_1,\dots,y_n,c_1,\dots,c_m)^T = 0$.
For example, \name(L, 1) returns a basis for $\Ker~L \cap R[x]$,
the space of all the polynomial solutions of $L y = 0$.}
\seealso{exteriorKernel(\this),\\
polynomialKernel(LODOPolynomialSolutions)}
#endif
		rationalSolution: (EQ, RF) -> Partial RF;
		rationalSolution: (Rxd, RF) -> Partial RF;
#if ASDOC
\aspage{rationalSolution}
\Usage{\name(L,g)}
\Signatures{
\name: & (Rxd, Quotient Rx) $\to$ Partial Quotient Rx\\
\name: &
(HolonomicEquation(R, Rx, Rxd), Quotient Rx) $\to$ Partial Quotient Rx\\
}
\Params{
{\em L} &              Rxd              & a differential equation\\
        & HolonomicEquation(R, Rx, Rxd) &\\
{\em g} & Quotient Rx & a fraction\\
}
\Retval{Returns $f$ such that $L f = g$ or \failed~if
$L y = g$ has no solution in $R(x)$.}
\Remarks{\name($L,0$) returns $0$ only when $L y = 0$ has no
nonzero rational solution.}
\seealso{polynomialSolution(LODOPolynomialSolutions)}
#endif
} == add {
	local field?:Boolean	== R has Field;
	rationalKernel(L:Rxd):V RF == { import from EQ; rationalKernel(L::EQ); }
	rationalKernel(L:EQ):V RF  		== polKern(L, denom L);
	rationalKernel(L:EQ, p:PI Rx):V RF	== polKern(L, denom(L, p));

	rationalKernel(L:EQ, g:V RF):(V RF, M R) == {
		import from I, RF;
		assert(#g > 0);
		#g = 1 and zero?(g.1) => {		-- homogeneous equation
			K := rationalKernel L;
			zero?(#K)=> (zero 1,zero(1,2));	-- no nonzero solutions
			(K, zero(1, next(#K)));		-- nontrivial solutions
		}
		polKern(L, denom(L, g), g);
	}

	rationalSolution(L:EQ, g:RF):Partial RF == {
		import from I, R, V R, List V R, M R, Rx, V RF;
		zero? g => {
			K := rationalKernel L;
			#K = 0 => [0];
			[K.1];
		}
		vg:V RF := zero 1;
		vg.1 := g;
		(h, m) := rationalKernel(L, vg);
		(dim := #h) = 0 => failed;
		d := next dim;
		for v in nullSpace m repeat {
			assert(#v = d);
			~zero?(v.d) => {
				y:RF := 0;
				for i in 1..dim repeat
					y := add!(y, v.i::Rx * h.i);
				return [inv(v.d::Rx::RF) * y];
			}
		}
		failed;
	}

	rationalSolution(L:Rxd, g:RF):Partial RF == {
		import from EQ;
		rationalSolution(L::EQ, g);
	}

	rationalKernel(L:Rxd, g:V RF):(V RF, M R) == {
		import from EQ;
		rationalKernel(L::EQ, g);
	}

	local denom(L:EQ):PI Rx	== {
		import from Z, SING;
		denom(L, (s:SING):Z +-> degreeBound(s, 1));
	}

	local denom(L:EQ, g:V RF):PI Rx == {
		import from Z, SING, List SING, BalancedFactorization(R, Rx);
		import from Rx, Partial Rx, V Rx, List Rx, Rxd;
		import from VectorOverQuotient(Rx, RF);
		TRACE("ratsol::denom:L = ", L);
		TRACE("ratsol::denom:g = ", g);
		-- part corresponding to the singularities of L
		d := denom(L, (s:SING):Z +-> degreeBound(s, g));
		s:Rx := 1;	-- will contain all the singularities of L
		for sing in finiteSingularities L repeat s := s * center sing;
		nL := degree(op := operator L);
		local m:Z;
		-- analyze the poles of g which are NOT singularities of L
		(dg, gp) := makeIntegral g;	-- g = gp / d
		for trm in balancedFactor(dg, cons(dg,coefficients op)) repeat {
			(a, n) := trm;		-- nu_a(g) = -n
			u := exactQuotient(s, a);
			if failed? u then {	-- not a singularity of L
				nu := order a;
				m := 0;		-- will be min(nu(a_i) - i)
				for i in 0..nL
					| ~zero?(c:=coefficient(op,i)) repeat
					  if (mm := nu(c) - i) < m then m := mm;
				if (m := m + n) > 0 then d := times!(d, a, m);
			}
		}
		TRACE("ratsol::denom:d = ", d);
		d;
	}

	exponentialDenom(L:EQ):PI Rx == {
		import from SING;
		denom(L, exponentialDegreeBound);
	}

	rationalKernel(L:EQ, p:Rx):V RF	== {
		import from Z, PI Rx;
		rationalKernel(L, term(squareFreePart p, 1));
	}

	exteriorKernel(L:Rxd, n:Z):V RF == {
		import from I, Rx, BalancedFactorization(R, Rx);
		assert(n >= 1);
		n > (d := degree L) => zero(1);
		one? n or n = d => rationalKernel L;
		rationalKernel(exteriorPower(L, n),
			balancedFactor(leadingCoefficient L, coefficients L));
	}

	rationalKernel(L:Rxd, p:Rx):V RF == {
		import from EQ;
		rationalKernel(L::EQ, p);
	}

	rationalKernel(L:Rxd, p:PI Rx):V RF == {
		import from EQ;
		rationalKernel(L::EQ, p);
	}

	-- look for solutions of the form p/d
	local polKern(L:EQ, d:PI Rx):V RF == {
		import from I, Z, Rx, RF, Rxd, V Rx;
		import from LODOPolynomialSolutions(R, Rx, Rxd);
		import from LinearOrdinaryDifferentialOperatorTools(Rx, Rxd);
		START__TIME;
		noden? := zero? degree(dd := expand d);
		sp := {
			noden? => polynomialKernel L;
			(Lprime, alpha) := twist(operator L, d);
			Lprime := primitivePart Lprime;
			TIME("ratsol::polKern: new operator at ");
			TRACE("ratsol::polKern, new operator = ", Lprime);
			polynomialKernel Lprime;
		}
		TIME("ratsol::polKern: polynomial solutions at ");
		v:V RF := new(n := #sp, 0);
		for i in 1..n repeat v.i := { noden? => sp.i::RF; sp.i / dd; }
		v;
	}

	-- look for solutions of the form p/d
	local polKern(L:EQ, d:PI Rx, g:V RF):(V RF, M R) == {
		import from I, Z, Rx, RF;
		TRACE("ratsol::polKern:L = ", L);
		TRACE("ratsol::polKern:d = ", d);
		TRACE("ratsol::polKern:g = ", g);
		(sp, mat) := polKern(L, d, g, dd := expand d);
		one? dd => (sp, mat);
		ddd := inv(dd::RF);
		v := new(n := #sp, 0);
		for i in 1..n repeat v.i := ddd * sp.i;
		TRACE("ratsol::polKern:v = ", v);
		TRACE("ratsol::polKern:mat = ", mat);
		(v, mat);
	}

	-- look for solutions of the form p/d, returns p only
	-- there could be a constant denominator if R is not a field
	local polKern(L:EQ, d:PI Rx, g:V RF, dd:Rx):(V RF, M R) == {
		import from Z, Rx, RF, Rxd;
		import from LinearOrdinaryDifferentialOperatorTools(Rx, Rxd);
		TRACE("ratsol::polKern:L = ", L);
		TRACE("ratsol::polKern:d = ", d);
		TRACE("ratsol::polKern:g = ", g);
		TRACE("ratsol::polKern:dd = ", dd);
		zero? degree dd => polKern(L, dd::RF, g);
		-- Lprime(z) = alpha d L(z/d)
		(Lprime, alpha) := twist(operator L, d);
		TRACE("ratsol::polKern:Lprime = ", Lprime);
		TRACE("ratsol::polKern:alpha = ", alpha);
		(beta, Lprime) := primitive Lprime;
		TRACE("ratsol::polKern:beta = ", beta);
		TRACE("ratsol::polKern:Lprime = ", Lprime);
		polKern(Lprime::EQ, (alpha * dd) / beta, g);
	}

	-- look for polynomial solutions of L p = f g
	-- there could be a constant denominator if R is not a field
	local polKern(L:EQ, f:RF, g:V RF):(V RF, M R) == {
		import from I, Z, Rx, V Rx, VectorOverQuotient(Rx, RF);
		import from LODOPolynomialSolutions(R, Rx, Rxd);
		TRACE("ratsol::polKern:L = ", L);
		TRACE("ratsol::polKern:f = ", f);
		TRACE("ratsol::polKern:g = ", g);
		v:V RF := new(n := #g, 0);
		for i in 1..n repeat v.i := f * g.i;
		(d, w) := makeIntegral v;	-- w = d v is primitive
		TRACE("ratsol::polKern:d = ", d);
		TRACE("ratsol::polKern:w = ", w);
		zero? degree d => {
			(sp, mat) := polynomialKernel(L, w);
			noden? := one? d;
			v:V RF := new(n := #sp, 0);
			for i in 1..n repeat
				v.i := { noden? => sp.i::RF; sp.i / d }
			(v, mat);
		}
		-- TEMPORARY: FOR EFFICIENCY,
		-- MUST DO A EUCLIDEAN DIVISION w.i = d q.i + r.i
		-- AND SOLVE L p = sum_i c_i q_i
		-- WITH THE ADDITIONAL CONDITIONS sum_i c_i r_i = 0
		import from Rxd;
		(sp, mat) := polynomialKernel(d * operator L, w);
		v:V RF := new(n := #sp, 0);
		for i in 1..n repeat v.i := sp.i::RF;
		(v, mat);
	}

	local denom(L:EQ, p:PI Rx):PI Rx == {
		import from Z, Rx, SING, List SING;
		TRACE("ratsol::denom, L = ", L);
		TRACE("ratsol::denom, p = ", p);
		START__TIME;
		d:PI(Rx) := 1;
		TRACE("ratsol::denom, denom = ", d);
		for s in analyzedSingularities L repeat {
			for trm in p repeat {
				(a, n) := trm;
				TRACE("::singularity = ", a);
				if ((m := degreeBound s) > 0)
					and (degree(g := gcd(a, center s)) > 0)
						then d := times!(d, g, m);
				TRACE("ratsol::denom, denom = ", d);
			}
		}
		TIME("ratsol::denom, analyzed singularities at ");
		for s in analyze!(L, p) repeat
			if (m := degreeBound s) > 0 then
				d:= times!(d, center s, m);
		TIME("ratsol::denom, other singularities at ");
		TRACE("ratsol::denom, final denom = ", d);
		d;
	}

	local denom(L:EQ, bound: SING -> Z):PI Rx == {
		import from Z, SING, List SING;
		TRACE("ratsol::denom, L = ", L);
		d:PI(Rx) := 1;
		TRACE("::denom = ", d);
		for s in finiteSingularities L repeat
			if (m := bound s) > 0 then d := times!(d, center s, m);
		TRACE("::final denom = ", d);
		d;
	}
}

#if SUMITTEST
---------------------- test ratsol.as --------------------------
#include "sumittest"

macro {
	Z == Integer;
	Q == Quotient Z;
	Qx == DenseUnivariatePolynomial(Q, "x");
	Fx == Quotient Qx;
	OP == LinearOrdinaryDifferentialOperator(Qx, "D");
}

polys():Boolean == {
	macro DIM == 5;
	import from SingleInteger, Z, Q, Qx, OP, LODORationalSolutions(Q,Qx,OP);
	import from Vector Fx, Fx;
	x:Qx := monom;
	dx:OP := monom;
	op := dx^DIM;
	sols := rationalKernel op;
	n := #sols;
	n ~= DIM => false;
	vd:Vector Z := zero n;
	for i in 1..n repeat {
		~one? denominator(sols.i) => return false;
		vd(next retract degree numerator(sols.i)) := 1;
	}
	for i in 1..n repeat zero?(vd.i) => return false;
	true;
}
	
solve3():Boolean == {
	import from SingleInteger, Z, Q, Qx, OP, LODORationalSolutions(Q,Qx,OP);
	import from Vector Fx, Fx;
	x:Qx := monom;
	dx:OP := monom;
	op := (x^9+x^3)*dx^3 + 18*x^8*dx^2-90*x*dx-30*(11*x^6 - (3@Z)::Qx)::OP;
	sols := rationalKernel op;
	n := #sols;
	f:Fx := x::Fx;
	if n > 0 then f := sols.1;
	n = 1 and zero? differentiate(((x^6+1)/x) * f);
}

print << "Testing rational solutions of Q[x,d/dx]..." << newline;
sumitTest("D^k", polys);
sumitTest("3rd order", solve3);
print << newline;
#endif

