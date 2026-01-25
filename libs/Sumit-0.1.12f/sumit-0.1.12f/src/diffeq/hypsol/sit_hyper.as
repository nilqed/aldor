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
------------------------------ sit_hyper.as ------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it ©INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I   == MachineInteger;
	Z   == Integer;
	V   == Vector;
	M   == DenseMatrix;
	A   == PrimitiveArray;
	Rx  == Fraction RX;
	Fx  == Fraction FX;
	FFX == UnivariateFactorialPolynomial(F, FX);
	PRX == Product RX;
	FR  == FractionalRoot R;
}

#if ALDOC
\thistype{LinearOrdinaryRecurrenceHypergeometricSolutions}
\History{Manuel Bronstein}{17/8/2000}{created}
\Usage{import from \this(R, F, $\iota$, RX, RXE, FX)}
\Params{
{\em R} & \astype{GcdDomain} & A gcd domain\\
        & \astype{FactorizationRing} & \\
{\em F} & \astype{Field} & A field containing R\\
$\iota$ & $R \to F$ & Injection from R into F\\
{\em RX} & \astype{UnivariatePolynomialCategory} R & Polynomials over R\\
{\em RXE} & \astype{LinearOrdinaryRecurrenceCategory} RX & Recurrences over RX\\
{\em FX} & \astype{UnivariatePolynomialCategory} F & Polynomials over F\\
}
\Descr{\this(R, F, $\iota$, RX, RXE, FX) provides a hypergeometric solver
for linear ordinary recurrence operators with polynomial coefficients.}
\begin{exports}
\asexp{allHypergeometricSolutions}:
& RXE $\to$
\astype{List} \builtin{Cross}(Fx, \astype{Vector} FX) &
All solutions\\
\asexp{hypergeometricSolution}:
& RXE $\to$ \astype{Partial} Fx &
A solution\\
\end{exports}
\begin{aswhere}
Fx &==& \astype{Fraction} FX\\
\end{aswhere}
#endif

LinearOrdinaryRecurrenceHypergeometricSolutions(
	R:Join(GcdDomain, FactorizationRing), F:Field, inj: R -> F,
	RX: UnivariatePolynomialCategory R,
	RXE: LinearOrdinaryRecurrenceCategory RX,
	FX: UnivariatePolynomialCategory F): with {
		allHypergeometricSolutions: RXE -> List Cross(Fx, V FX);
#if ALDOC
\aspage{allHypergeometricSolutions}
\Usage{\name~L}
\Signature{RXE}
{\astype{List} \builtin{Cross}(\astype{Fraction} FX, \astype{Vector} FX)}
\Params{
{\em L} & RXE & A linear ordinary recurrence operator\\
}
\Retval{Returns $[]$ if $L y = 0$ has no hypergeometric solution over $R$,
\ie a solution $y(n)$ such that $y(n+1)/y(n)$ is a fraction of polynomials
in $RX$.
Otherwise, it returns a list of pairs of the form
$(\gamma(n), [p_1(n),\dots,p_m(n)])$
such that the hypergeometric solutions of $L y = 0$ are exactly all
the $y(n)$'s such that
$$
\frac{y(n+1)}{y(n)} =
\gamma(n) \frac{\sum_{i=1}^m c_i p_i(n+1)}{\sum_{i=1}^m c_i p_i(n)}
$$
for some pair in the list, where the $c_i$'s are arbitrary constants.
In addition, if $p_1,\dots,p_m$ are linearly independent over the constants
in each pair of the list.}
\Remarks{A return value of $[]$ proves that there
are no hypergeometric solutions over $R$, but there could be hypergeometric
solutions over the algebraic closure of its fraction field.}
#endif
		hypergeometricSolution: RXE -> Partial Fx;
#if ALDOC
\aspage{hypergeometricSolution}
\Usage{\name~L}
\Signature{RXE}{\astype{Partial} \astype{Fraction} FX}
\Params{
{\em L} & RXE & A linear ordinary recurrence operator\\
}
\Retval{Returns \failed if $L y = 0$ has no hypergeometric solution over $R$,
\ie a solution $y(n)$ such that $y(n+1)/y(n)$ is a fraction of polynomials
in $RX$.
Otherwise, it returns $f(n)$
such that any solution of $y(n+1) = f(n) y(n)$
is also a solution of $L y = 0$.}
\Remarks{Note that \name~does not attempt to return more than one
hypergeometric solution, so if it finds one, there could
be some others. In addition, a return value of $[]$ proves that there
are no hypergeometric solutions over $R$, but there could be hypergeometric
solutions over the algebraic closure of its fraction field.}
#endif
} == add {
	local hash?:Boolean		== RX has HashType;
	local identity(p:FX):FX		== p;
	local sigma(p:RX, n:Z):RX	== { import from R;translate(p,(-n)::R)}

	local sigma(n:Z):FX -> FX == {
		import from F;
		zero? n => identity;
		nf := (-n)::F;
		(p:FX):FX +-> translate(p, nf);
	}

	local sigma(f:Fx, n:Z):Fx == {
		sig := sigma n;
		sig(numerator f) / sig(denominator f);
	}

	-- returns the adjacency matrix of the bipartite dispersion graph:
	-- the left nodes are the irreducible factors a_i of a
	-- the right nodes are the irreducible factors b_j of b
	-- an edge between a_i and b_j means that their spread is not empty
	-- also returns the vector [a_1,...,a_i,...] for indexing purposes
	local dispersionGraph(a:PRX, b:PRX):(M I, V RX) == {
		import from I, Z, RX;
		m := zero(r := #a, c := #b);
		v := zero r;
		for i in 1..r for t in a repeat {
			(ai, e) := t;
			v.i := ai;
			for j in 1..c for s in b repeat {
				(bj, e) := s;
				-- since ai and bj are irreducible, a nec. cond.
				-- for an edge is that they have equal degree
				if degree(ai) = degree(bj) and
					dispersion(ai,bj) >= 0 then m(i,j):=1$I;
			}
		}
		(m, v);
	}

	-- returns the largest factor of b whose subproducts are all
	-- guaranteed to have an empty spread with a
	-- m and va describe the dispersion graph
	local filter(b:PRX, m:M I, va:V RX, a:PRX):PRX == {
		import from Boolean, I, RX;
		TRACE("hyper::filter: b = ", b);
		TRACE("hyper::filter: m = ", m);
		TRACE("hyper::filter: va = ", va);
		TRACE("hyper::filter: a = ", a);
		v:V I := zero(c := numberOfColumns m);
		TRACE("hyper::filter: c = ", c);
		for t in a repeat {
			(p, e) := t;
			TRACE("hyper::filter: p = ", p);
			(w, pos) := find(p, va);	-- va.pos = p
			TRACE("hyper::filter: pos = ", pos);
			assert(~empty? w);
			for j in 1..c repeat if one? m(pos,j) then v.j := 1;
		}
		-- at this point v.j = 0 means keep factor j of b
		bb:PRX := 1;
		for j in 1..c for t in b repeat {
			(p, e) := t;
			if zero?(v.j) then bb := times!(bb, p, e);
		}
		TRACE("hyper::filter: returning ", bb);
		bb;
	}

	hypergeometricSolution(L:RXE):Partial Fx == {
		import from Boolean, I, Z, Fx, V FX, List Cross(Fx, V FX);
		empty?(l := hyper(L, true)) => failed;
		assert(empty? rest l);
		(gamma, v) := first l;
		p := v.1;
		[gamma * (sigma(1)(p) / p)];
	}

	allHypergeometricSolutions(L:RXE):List Cross(Fx, V FX) == {
		import from Boolean;
		hyper(L, false);
	}

	local hyper(L:RXE, oneSol?:Boolean):List Cross(Fx, V FX) == {
		import from Z, RX, PRX, V FX;
		assert(~zero? L);
		TRACE("hyper::hyper: L = ", L);
		TRACE("hyper::hyper: oneSol? = ", oneSol?);
		TIMESTART;
		L := primitivePart L;
		TIME("hyper::hyper: pp(L) at ");
		TRACE("hyper::hyper: pp(L) = ", L);
		(p0, n0) := trailingMonomial L;
		L := shift(L,-n0);		-- make trailing degree 0
		(pn, n) := leadingMonomial L;
		zero? n => empty;
		(c0, fp0) := factor p0;
		(cn, fpn) := factor sigma(pn, 1 - n);
		TIME("hyper::hyper: factorisations at ");
		(m, v) := dispersionGraph(fp0, fpn);
		TIME("hyper::hyper: dispersion graph at ");
		hash? => hashSolve(L, fp0, fpn, m, v, n0, oneSol?);
		sig!:V FX -> V FX := map! sigma(-n0);
		l:List Cross(Fx, V FX) := empty;
		for a in divisors fp0 repeat {
			for b in divisors filter(fpn, m, v, a) repeat {
				sol := tryPair(L, expand a, expand b, oneSol?);
				if ~empty? sol then {
					for pair in sol repeat {
						(gamma, w) := pair;
						l := cons((sigma(gamma, -n0),
								sig! w), l);
					}
					oneSol? => return l;
				}
			}
		}
		l;
	}

	if R has HashType then {
		macro HASH == HashTable(RX, List FR);

		local hashSolve(L:RXE, fp0:PRX, fpn:PRX, m:M I, v:V RX, n0:Z,
			oneSol?:Boolean):List Cross(Fx, V FX) == {
			import from I, V FX, HASH;
			sz := #fp0 + #fpn;
			sz := { sz > 9 => 7000; shift(1, sz); }
			ht := table(nextPrime(sz)$SmallPrimes);
			sig!:V FX -> V FX := map! sigma(-n0);
			l:List Cross(Fx, V FX) := empty;
			for a in divisors fp0 repeat {
				for b in divisors filter(fpn, m, v, a) repeat {
					sol := hashTryPair(L, expand a,
							expand b, oneSol?, ht);
					if ~empty? sol then {
						for pair in sol repeat {
							(gamma, w) := pair;
							l := cons((sigma(gamma,
								-n0),sig! w),l);
						}
						oneSol? => return l;
					}
				}
			}
			l;
		}

		-- htable is a table of roots of past indicial equations
		local hashTryPair(L:RXE, a:RX, b:RX, oneSol?:Boolean,
			htable:HASH):List Cross(Fx, V FX) == {
			import from Boolean, List FR, V FX;
			TRACE("hyper::hashTryPair: L = ", L);
			TRACE("hyper::hashTryPair: a = ", a);
			TRACE("hyper::hashTryPair: b = ", b);
			TIMESTART;
			(p, L1) := twist(L, a, b);
			TIME("hyper::hashTryPair: operator twisted at ");
			TRACE("hyper::hashTryPair: p = ", p);
			TRACE("hyper::hashTryPair: L1 = ", L1);
			l:List Cross(Fx, V FX) := empty;
			for z in roots!(htable, p) repeat {
				(gamma, sol) := tryZ(L1, a, b, z);
				if ~empty? sol then {
					l := cons((gamma, sol), l);
					oneSol? => return l;
				}
			}
			TIME("hyper::hashTryPair: done at ");
			l;
		}

		local roots!(htable:HASH, p:RX):List FR == {
			import from Partial List FR;
			failed?(u := find(htable, p)) => {
				htable.p := [fractionalRoots p];
			}
			retract u;
		}
	}

	local tryPair(L:RXE, a:RX,b:RX,oneSol?:Boolean):List Cross(Fx,V FX) == {
		import from V FX;
		(p, L1) := twist(L, a, b);
		l:List Cross(Fx, V FX) := empty;
		for z in fractionalRoots p repeat {
			(gamma, sol) := tryZ(L1, a, b, z);
			if ~empty? sol then {
				l := cons((gamma, sol), l);
				oneSol? => return l;
			}
		}
		l;
	}

	-- returns (gamma, [p1,...,pm]) such that the pi's are lin. indep
	-- and (E - gamma \sum_i c_i \sigma(p_i) / \sum_i c_i p_i) divides L
	local tryZ(L:RXE, a:RX, b:RX, z:FR):(Fx, V FX) == {
		import from I, Z, R, FX, Fx, FFX, V FFX, FR,
		  LinearOrdinaryOperatorPolynomialSolutions(R,F,inj,RX,RXE,FFX);
		import from UnivariateFreeFiniteAlgebra2(R, RX, F, FX);
		TIMESTART;
		(num, den) := value z;
		zero? num => (0, empty);
		L2 := twist(L, num, den);
		TIME("hyper::tryZ: operator scaled at ");
		TRACE("hyper::tryZ: L2 = ", L2);
		K := kernel L2;
		TIME("hyper::tryZ: polynomial kernel at ");
		TRACE("hyper::tryZ: K = ", K);
		f := map inj;
		gamma := f(num * a) / f(den * b);
		sol := [expand c for c in K];
		TIME("hyper::tryZ: expanded solutions at ");
		(gamma, sol);
	}

	-- return d^m \sum_{i=0}^m (n/d)^i p_i E^i
	-- where L = \sum_{i=0}^m p_i E^i
	local twist(L:RXE, n:R, d:R):RXE == {
		import from I, Z, RX;
		m := machine degree L;
		ni:A R := new next m;
		di:A R := new next m;
		ni.0 := 1;
		di.0 := 1;
		for i in 1..m repeat {
			ni.i := n * ni(prev i);
			di.i := d * di(prev i);
		}
		LL:RXE := 0;
		for term in L repeat {
			(c, e) := term;
			ee := machine e;
			LL := add!(LL, ni(ee) * di(m - ee) * c, e);
		}
		LL;
	}

	-- returns indicial equation and twisted operator for given a and b
	local twist(L:RXE, a:RX, b:RX):(RX, RXE) == {
		import from Boolean, I, Z;
		m := machine degree L;
		ai:A RX := new next m;
		bi:A RX := new next m;
		ai.0 := 1;
		bi.0 := 1;
		for i in 1..m repeat {
			ai.i := sigma(a, prev(i)::Z) * ai(prev i);
			bi.i := sigma(b, (m - i)::Z) * bi(prev i);
		}
		LL:RXE := 0;
		dmax:Z := -1;
		for term in L repeat {
			(c, e) := term;
			ee := machine e;
			p := ai(ee) * bi(m - ee) * c;
			if ~zero?(p) then {
				LL := add!(LL, p, e);
				d := degree p;
				if d > dmax then dmax := d;
			}
		}
		eq:RX := 0;
		for term in LL repeat {
			(c, e) := term;
			if dmax = degree c then
				eq := add!(eq, leadingCoefficient c, e);
		}
		(primitivePart eq, LL);
	}
}

#if SUMITTEST
---------------------- test sit_hyper.as --------------------------
#include "sumittest"

macro {
	Z == Integer;
	ZN == DenseUnivariatePolynomial(Z, -"n");
	ZNE == LinearOrdinaryRecurrence(Z, ZN, -"E");
	Q == Fraction Z;
	QN == DenseUnivariatePolynomial(Q, -"n");
	Qn == Fraction QN;
}

import from Symbol;

local solve(L:ZNE):Partial Qn == {
	import from Q, QN, LinearOrdinaryRecurrenceHypergeometricSolutions(Z,_
							Q, coerce, ZN, ZNE, QN);
	hypergeometricSolution L;
}

local nosols():Boolean == {
	import from Partial Qn;
	n:ZN := monom;
	E:ZNE := monom;
	L := (n + 1) * E*E + E + (n-1)::ZNE;
	failed? solve L;
}

local onesol():Boolean == {
	import from Qn, Partial Qn;
	n:ZN := monom;
	E:ZNE := monom;
	nn:QN := monom;
	L := E*E + E - (n*n)::ZNE;
	~failed?(u := solve L) and zero?(retract(u) + nn::Qn);
}

stdout << "Testing sit__hyper..." << endnl;
sumitTest("no solutions", nosols);
sumitTest("one solution", onesol);
stdout << endnl;
#endif

