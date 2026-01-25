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
------------------------------ sys2lodo.as ------------------------------
#include "sumit"

macro {
	I == SingleInteger;
	Z == Integer;
	V == Vector;
	M == DenseMatrix;
	SYS == LinearOrdinaryDifferentialSystem;
}

#if ASDOC
\thistype{System2LinearOrdinaryDifferentialOperator}
\History{Manuel Bronstein}{6/5/97}{created}
\Usage{ import from \this(R, C)}
\Params{
{\em R} & CommutativeRing & Coefficients of the operators\\
{\em C} & LinearOrdinaryDifferentialOperatorCategory R &
Differential operators\\
}
\Descr{\this(R, C) provides conversions between linear ordinary
differential operators and systems with coefficients in R.}
\begin{exports}
companionSystem: & C $\to$ SYS R & Associated companion system\\
\end{exports}
\begin{exports}[if R has IntegralDomain then]
cycle: & (SYS R, Vector R) $\to$ (C, DenseMatrix R, R) & Cycle of a vector\\
cyclicVector: & SYS R $\to$ (C, DenseMatrix R, R) & Cyclic vector\\
exteriorPower: & (C, Integer) $\to$ SYS R & Exterior power\\
symmetricPower: & (C, Integer) $\to$ SYS R & Symmetric power\\
\end{exports}
\begin{aswhere}
SYS &==& LinearOrdinaryDifferentialSystem\\
\end{aswhere}
#endif

System2LinearOrdinaryDifferentialOperator(R:CommutativeRing,
	C:LinearOrdinaryDifferentialOperatorCategory R): with {
		companionSystem: C -> SYS R;
#if ASDOC
\aspage{companionSystem}
\Usage{\name~L}
\Signature{C}{LinearOrdinaryDifferentialSystem R}
\Params{ {\em L} & C & A differential operator of positive order\\ }
\Retval{Returns the companion system $a Y' = A Y$ equivalent to $L y = 0$.}
\Remarks{\name~is not applicable to operators of order $0$.}
#endif
		if R has IntegralDomain then {
			cycle: (SYS R, V R) -> (C, M R, R);
#if ASDOC
\aspage{cycle}
\Usage{(L, P, a) := \name(S, v)}
\Signature{(LinearOrdinaryDifferentialSystem R, Vector R)}{(C,DenseMatrix R,R)}
\Params{
{\em S} & LinearOrdinaryDifferentialSystem R & A differential system\\
{\em v} & Vector R & A vector with coefficients in R\\
}
\Retval{Returns $L = \sum_{i=0}^n a_i D^i$, a matrix $P$ with coefficients in
$R$ and an element $a\in R$ such that:
$v,\nabla v,\dots,\nabla^{n-1} v$ are linearly independent over the quotient
field of $R$,
$$
\sum_{i=0}^n a_i \nabla^i v = 0\,,
$$
and the columns of $P$ are $v, a \nabla v, \dots, a^{n-1} \nabla^{n-1} v$,
where $\nabla Y = Y' - a^{-1} A Y$ is the differential operator corresponding
to the system $S$.}
\seealso{cyclicVector}
#endif
			cyclicVector: SYS R -> (C, M R, R);
#if ASDOC
\aspage{cyclicVector}
\Signature{LinearOrdinaryDifferentialSystem R}{(C, DenseMatrix R, R)}
\Usage{(L, P, a) := \name~S}
\Params{
{\em S} & LinearOrdinaryDifferentialSystem R & A differential system\\
}
\Retval{Returns the cycle $(L, P, a)$ of the vector $v$ given by the
first column of $P$. That vector is chosen so that $L$ has maximal order,
\ie~the order of the system $S$.}
\seealso{cycle}
#endif
			exteriorPower: (C, Z) -> SYS R;
#if ASDOC
\aspage{exteriorPower}
\Usage{\name(L, n)}
\Signature{(C, Integer)}{LinearOrdinaryDifferentialSystem R}
\Params{
{\em L} & C & A differential operator\\
{\em n} & Integer & A positive integer\\
}
\Retval{Returns the $\sth{n}$ associated system of $L$.}
\Remarks{$n$ must be stricly smaller than the order of $L$.}
\seealso{symmetricPower(\this)}
#endif
			symmetricPower: (C, Z) -> SYS R;
#if ASDOC
\aspage{symmetricPower}
\Usage{\name(L, n)}
\Signature{(C, Integer)}{LinearOrdinaryDifferentialSystem R}
\Params{
{\em L} & C & A differential operator\\
{\em n} & Integer & A positive integer\\
}
\Retval{Returns $a Y' = A Y$ where the derivation induced by L on
the homogeneous polynomials of degree $n$ in the variables
$Y_1,\dots,Y_{\deg(L)}$ is given by $p \to Dp - a^{-1} A p$.}
\Remarks{\name~is not applicable to operators of order $0$.}
\seealso{exteriorPower(\this)}
#endif
		}
} == add {
	companionSystem(L:C):SYS R == {
		ASSERT(~zero? L);
		import from SingleInteger, Z, R, Partial R, DenseMatrix R;
		m:SingleInteger := retract degree L;
		ASSERT(m > 0);
		a := leadingCoefficient L;
		failed?(u := reciprocal a) => ffsystem(L, m, a);
		mainv := - retract u;
		mat := zero(m, m);
		for i in 1..prev m repeat mat(i, next i) := 1;
		for term in reductum L repeat {
			(c, n) := term;
			mat(m, next retract n) := mainv * c;
		}
		system(1, mat);
	}

	local ffsystem(L:C, m:SingleInteger, a:R):SYS R == {
		import from SingleInteger, Z, R, DenseMatrix R;
		mat := zero(m, m);
		for i in 1..prev m repeat mat(i, next i) := a;
		for term in reductum L repeat {
			(c, n) := term;
			mat(m, next retract n) := - c;
		}
		system(a, mat);
	}

	if R has IntegralDomain then {
		macro {
			RID  == R pretend IntegralDomain;
			SP   == SymmetricPower(RID, C, n, m);
			FFSP == FactorFreeSymmetricPower(RID, C, n, m, p);
		}

		local diff:Derivation R		== derivation$C;
		symmetricPower(L:C, N:Z):SYS R	== extSymPow(L, N, matsympow);
		exteriorPower(L:C, N:Z):SYS R	== extSymPow(L, N, matextpow);

		local connection(A:M R)(v:V R):V R == {
			import from I, R;
			w := A * v;
			for i in 1..#w repeat w.i := diff(v.i) - w.i;
			w;
		}

		cycle(s:SYS R, v:V R):(C, M R, R) == {
			import from R, Partial R;
			TRACE("cycle: v = ", v);
			(p, A) := matrix s;
			failed?(u := reciprocal p) => annihilator(p, A, v);
			annihilator(retract(u) * A, v);
		}

		-- case when the lhs coeff is not a unit in R
		local annihilator(p:R, A:M R, v:V R):(C, M R, R) == {
			import from FractionFreeCyclicVector(RID, C, p);
			(L, m) := firstAnnihilator(A, v);
			(L, m, p);
		}

		-- case when the lhs coeff is 1
		local annihilator(A:M R, v:V R):(C, M R, R) == {
			import from I, Z, List V R, CyclicVector(RID, C, V R);
			(L, l) := firstAnnihilator(connection A,
							(w:V R):V R +-> w, v);
			n := retract degree L;
			ASSERT(#l = next n);
			ASSERT(n <= cols A);
			P:M R := zero(n, n);
			j := n;
			for vec in rest l repeat {
				for i in 1..n repeat P(i, j) := vec.i;
				j := prev j;
			}
			(L, P, 1);
		}

		local random!(w:V R):V R == {
			import from I, Z, R, RandomNumberGenerator;
			r := randomGenerator 1;
			x := sample$R;
			for i in 1..#w repeat
				w.i := r()::R + r() * x;
			w;
		}
			
		cyclicVector(s:SYS R):(C, M R, R) == {
			import from I, Z, V R;
			n := order s;
			w:V R := zero(nn := retract n);
			-- try first e_1,...,e_n
			for i in 1..nn repeat {
				w.i := 1;
				(L, P, a) := cycle(s, w);
				n = degree L => return(L, P, a);
				w.i := 0;
			}
			-- try then n random combinations
			for i in 1@I..10 repeat {
				(L, P, a) := cycle(s, random! w);
				n = degree L => return(L, P, a);
			}
			error "sys2lodo::cyclic vector: no vector worked";
		}

		local extSymPow(L:C, N:Z, f:(C, I, I, R) -> SYS R):SYS R == {
			import from I;
			ASSERT(N > 0);
			TRACE("sys2lodo::extSymPow: L = ", L);
			TRACE("sys2lodo::extSymPow: N = ", N);
			one? N => companionSystem L;
			f(L, retract N, retract degree L, leadingCoefficient L);
		}

		-- creating a new scope is necessary
		local matsympow(L:C, n:I, m:I, p:R):SYS R == {
			import from Partial R, DenseMatrix R;
			TRACE("sys2lodo::matsympow: L = ", L);
			TRACE("sys2lodo::matsympow: n = ", n);
			TRACE("sys2lodo::matsympow: m = ", m);
			TRACE("sys2lodo::matsympow: p = ", p);
			failed?(u := reciprocal p) =>
				system(symmetricPower(L)$FFSP);
			TRACE("sys2lodo::matsympow: u = ", retract u);
			system(1, symmetricPower(L, retract u)$SP);
		}

		-- creating a new scope is necessary
		local matextpow(L:C, n:I, m:I, p:R):SYS R == {
			import from Partial R, DenseMatrix R;
			ASSERT(n < m);
			failed?(u := reciprocal p) =>
				system(exteriorPower(L)$FFSP);
			system(1, exteriorPower(L, retract u)$SP);
		}
	}
}
