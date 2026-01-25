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
------------------------- order2 --------------------------
#include "sumit"

#if ASDOC
\thistype{SecondOrderLODOSolver}
\History{Manuel Bronstein}{2/7/96}{created}
\Usage{import from \this(R, Rx, Rxd, Py)}
\Params{
{\em R} & GcdDomain        & Coefficients of the polynomials\\
	& RationalRootRing & \\
{\em Rx} & UnivariatePolynomialCategory R & Coefficients of the operators\\
{\em Rxd} & LODO Rx & The differential operators\\
{\em Py} & UnivariatePolynomialCategory Quotient Rx &
For returning algebraic curves\\
}
\begin{aswhere}
LODO &==& LinearOrdinaryDifferentialOperatorCategory\\
\end{aswhere}
\Descr{\this(R, Rx, Rxd, Py) provides tools for solving second order
linear ordinary differential equations in $R[x,\frac d{dx}]$.}
\begin{exports}
Darboux: & Rxd $\to$ List Py & Minimal Darboux polynomials\\
Darboux: & (Rxd, Z) $\to$ List Py &
Darboux polynomials of given degree\\
Darboux: & (Rxd, Z, Quotient Rx) $\to$ List Py &
Darboux polynomial from an invariant\\
\end{exports}
\begin{aswhere}
Z &==& Integer\\
\end{aswhere}
#endif

macro {
	I	== SingleInteger;
	Z	== Integer;
	RR	== RationalRoot;
	RF	== Quotient Rx;
	HEQ	== HolonomicEquation(R, Rx, Rxd);
	Rxy	== DenseUnivariatePolynomial Rx;
}

SecondOrderLODOSolver(R: Join(GcdDomain, RationalRootRing),
			Rx:UnivariatePolynomialCategory R,
			Rxd:LinearOrdinaryDifferentialOperatorCategory Rx,
			Py: UnivariatePolynomialCategory RF): with {
		Darboux: Rxd -> List Py;
		Darboux: (Rxd, Z, RF) -> Py;
#if ASDOC
\aspage{Darboux}
\Usage{\name~L \\ \name(L, n, f)}
\Signatures{
\name: & Rxd $\to$ List Py\\
\name: & (Rxd, Integer, Quotient Rx) $\to$ Py\\
}
\Params{
{\em L} & Rxd & A second order differential equation\\
{\em n} & Integer & The degree of the Darboux polynomial\\
{\em f} & Quotient Rx & A rational solution of $\sympow{L}{n}$\\
}
\Retval{
\name~L returns Darboux polynomials for $L$ of lowest possible degree,
while \name(L,n,f) returns the Darboux polynomial for $L$ of degree $n$
corresponding to the solution $f$ of $\sympow{L}{n}$.
}
\Remarks{
If \name(L) returns $[0]$, then this proves that $L$ is irreducible and has no
nontrivial Darboux curves, and hence that $L y = 0$ has no Liouvillian
solutions. Because \name~uses a modular heuristic for computing the
exponential solutions of $L y = 0$ when it is not completely reducible,
it might return $[]$, in which case
then either $L y = 0$ is irreducible and $L y = 0$ has no Liouvillian solution,
or $L$ is reducible but not completely reducible, with the latter case
more probable. Please send an email to {\tt asharp@inf.ethz.ch} if you
have an example with coefficients in ${\bf Q}(x)$ on which \name~returns $[]$.
}
#endif
		factor: Rxd -> List Py;
} == add {
	local integer?:Boolean	== R has IntegerCategory;
	Darboux(L:Rxd):List Py	== Darboux(L, true);
	factor(L:Rxd):List Py	== Darboux(L, false);

	local unimodular?(L:Rxd):Boolean == {
		import from Z, RF;
		d := degree L;
		ASSERT(d > 0);
		logder?(coefficient(L, prev d) /$RF coefficient(L, d));
	}

	local logder?(f:RF):Boolean == {
		import from Z, Rx, Derivation Rx, Rxy, RR, List RR;
		zero?(a := numerator f) => true;
		d := denominator f;
		ASSERT(~zero? d);
		(dd := degree d) ~= next degree(a) => false;
		D := derivation$Rxd;
		r := resultant(lift d, lift a - monom$Rx * lift D d);
		sum:Z := 0;
		for rt in integerRoots r repeat sum := sum + multiplicity rt;
		sum = dd;
	}

	local lift(p:Rx):Rxy == {
		q:Rxy := 0;
		for term in p repeat {
			(c, n) := term;
			q := add!(q, c::Rx, n);
		}
		q;
	}

	-- returns (LL, s) where LL is the unimodular transform of L
	-- and s is the shift for the curves (c(y) becomes c(y + s))
	-- s = 0 iff L is already unimodular, in which case LL = L
	local unimodularize(E:HEQ):(HEQ, RF) == {
		import from Z, RF, Rx, Derivation Rx, Rxd;
		unimodular?(L := operator E) => (E, 0);
		ASSERT(degree L = 2);
		D := derivation$Rxd;
		-- the transformed equation of a2 y'' + a1 y' + a0 y
		-- through  z = exp(int(a1/a2)/2) y
		-- is  4 a2^2 z'' + (4 a0 a2 - a1^2 + 2 a1 a2' - 2 a1' a2) z
		a0 := coefficient(L, 0);
		a1 := coefficient(L, 1);
		a2 := leadingCoefficient L;
		b2 := 4 * a2^2;
		b0 := 4 * a0 * a2 - a1^2 + 2 * a1 * D a2 - 2 * a2 * D a1;
		-- make the new operator primitive
		(g, c0, c2) := gcdquo(b0, b2);
		ASSERT(unit? gcd(c0, c2));
		((monomial(c2, 2) + c0::Rxd)::HEQ, a1 / (2 * a2));
	}

	-- only looks for reducible operators if alsoIrr? is false;
	local Darboux(L:Rxd, alsoIrr?:Boolean):List Py == {
		import from I, Z, RF, Vector RF, Py;
		import from LODORationalSolutions(R, Rx, Rxd);
		ASSERT(degree L = 2);
		-- check for rational solutions before transforming
		-- the equation to unimodular, since those might disappear
		START__TIME;
		m := #(V := rationalKernel(E := L::HEQ));
		TIME("Darboux: rational kernel at ");
		m > 0 => Darboux(L, 1, V, m);
		(U, s) := unimodularize E;
		TIME("Darboux: unimodular operator at ");
		LL := operator U;
		m := #(V := rationalKernel U);
		TIME("Darboux: unimodular rational kernel at ");
		m > 0 => translate(Darboux(LL, 1, V, m), s);
		-- check then for reducible and completely reducible
		m := #(V := rationalKernel(symmetricPower(LL, 2),
							leadingCoefficient LL));
		TIME("Darboux: quadratic kernel at ");
		m > 0 => translate(Darboux(LL, 2, V, m), s);
		knownIrr?:Boolean := false;
		if integer? then {
			(knownIrr?, curves) := heuristicDarboux L;
			~empty? curves => return curves;
		}
		TIME("Darboux: heuristic irreducibility at ");
		curves:List Py := { alsoIrr? => irrDarboux U; empty(); }
		TIME("Darboux: irreducible case at ");
		empty? curves => {
			knownIrr? => [0];
			curves;		-- UNABLE TO PROVE IRREDUCIBILITY HERE
		}
		translate(curves, s);
	}

	-- convert curves of the unimodular transform to curves of the operator
	local translate(curves:List Py, s:RF):List Py == {
		import from Py;
		empty? curves or zero? s => curves;
		q := monom + s::Py;
		[p(q) for p in curves];
	}

	-- Darboux curves for unimodular and assumed irreducible inputs
	local irrDarboux(E:HEQ):List Py == {
		import from List Z, I, Vector RF, Rxd;
		import from LODORationalSolutions(R, Rx, Rxd);
		import from BalancedFactorization(R, Rx);
		ASSERT(unimodular? L); ASSERT(degree L = 2);
		START__TIME;
		L := operator E;
		bl := balancedFactor(leadingCoefficient L, coefficients L);
		bl := refineInteger bl;	-- take out places of the form x - n
		TIME("irrDarboux: balanced factorization at ");
		m := #(V := rationalKernel(symmetricPower(L, 4), bl));
		TIME("irrDarboux: quartic kernel at ");
		m > 0 => Darboux(L, 4, V, m);
		if allRationalExponents? E then {
			for n in [6, 8, 12] repeat {
				m:=#(V:=rationalKernel(symmetricPower(L,n),bl));
				TIME("irrDarboux: symmetric kernel at ");
				m > 0 => return Darboux(L, n, V, m);
			}
		}
		empty();
	}

	if R has IntegerCategory then {
		-- TEMPORARY: COMPILER BUG (1.1.10b)
		macro RR == R pretend IntegerCategory;
		local heuristicDarboux(L:Rxd):(Boolean, List Py) == {
			import from R, Py,
				Union(factor:RF, irreducible:Z, failed:List Rx),
				HeuristicSecondOrderLODOFactorizer(RR, Rx, Rxd);
			u := rightFactor L;
			u case factor => (false, [monom - (u.factor)::Py]);
			(u case irreducible, empty());
		}
	}

	local first(p:Py, n:Z):Py == p;
	local refine(n:Z, p:Py):List Py == {
		ASSERT(n = degree p);
		import from Product Py;
		n > 5 => [p];		-- known to be irreducible
		(c, prod) := squareFree p;
		[first term for term in prod];
	}

	local Darboux(L:Rxd, n:Z, V:Vector RF, m:I):List Py == {
		ASSERT(m = #V);
		START__TIME;
		curves:List Py := empty();
		for i in 1..m repeat
			curves := concat!(curves, refine(n, Darboux(L,n,V.i)));
		TIME("Darboux: curve generated from kernel at ");
		curves;
	}

	-- construct the Darboux curve corresponding to v
	Darboux(L:Rxd, n:Z, v:RF):Py == {
		ASSERT(degree L = 2);
		ASSERT(n >= 1);
		ASSERT(~zero? v);
		p:Py := monomial(1, n);
		lc := leadingCoefficient L;
		a0 := coefficient(L, 0) / lc;
		a1 := coefficient(L, 1) / lc;
		-- ITERATION FOR NORMALIZED CURVE:
		bip1:RF := 1;
		bi := bn1 := - differentiate(v) / v;
		-- ITERATION FOR NON-NORMALIZED CURVE:
		-- bip1 := v;
		-- bi := - differentiate v;
		p := add!(p, bi, nm1 := prev n);
		for i in nm1 .. 1 by -1 repeat {
			-- ITERATION FOR NORMALIZED CURVE:
			b := (- differentiate(bi) + bn1 * bi + (i-n)*a1 * bi
			-- ITERATION FOR NON-NORMALIZED CURVE:
			-- b := (- differentiate(bi) + (i-n) * a1 * bi
					+ (i+1) * a0 * bip1) / ((n-i+1)::RF);
			p := add!(p, b, prev i);
			bip1 := bi;
			bi := b;
		}
		p;
	}
}
