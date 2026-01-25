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
------------------------- invariants.as --------------------------
-- Copyright Manuel Bronstein, 1998
-- Copyright INRIA, 1998

#include "sumit"

macro {
	I	== SingleInteger;
	Z	== Integer;
	Q	== Quotient R;
	RF	== Quotient Rx;
	V	== Vector;
	EQ	== HolonomicEquation(R, Rx, Rxd);
}

#if ASDOC
\thistype{LODOInvariant}
\History{Manuel Bronstein}{13/7/98}{created}
\Usage{import from \this(R, Rx, Rxd, Py)}
\Params{
{\em R} & GcdDomain        & Coefficients of the polynomials\\
        & RationalRootRing & \\
{\em Rx} & UnivariatePolynomialCategory R &
Coefficients of the operators\\
{\em Rxd} & LinearOrdinaryDifferentialOperatorCategory Rx &
The differential operators\\
{\em Py} & UnivariatePolynomialCategory Quotient Rx &
For returning algebraic curves\\
}
\Descr{\this(R, Rx, Rxd) computes dual first integrals for
differential equations.}
\begin{exports}
candidateRiccati: & \% $\to$ Py & Candidate Riccati polynomial\\
dualFirstIntegral: & \% $\to$ Vector Quotient Rx & Dual first integral\\
invariants: & (Rxd, Integer) $\to$ List \% & Basis of the invariants\\
invariants: & (HEQ, Integer) $\to$ List \% & Basis of the invariants\\
polynomial: & \% $\to$ Vector R & Invariant polynomial\\
value: & \% $\to$ Quotient Rx & Value of the invariante\\
\end{exports}
\begin{aswhere}
HEQ &==& HolonomicEquation(R, Rx, Rxd)\\
\end{aswhere}
#endif

LODOInvariant(R: Join(GcdDomain, RationalRootRing),
		Rx: UnivariatePolynomialCategory R,
		Rxd: LinearOrdinaryDifferentialOperatorCategory Rx,
		Py: UnivariatePolynomialCategory RF): with {
			candidateRiccati: % -> Py;
#if ASDOC
\aspage{candidateRiccati}
\Usage{\name~p}
\Signature{\%}{(RF, Py)}
\Params{ {\em p} & \% & An invariant\\ }
\Retval{Returns $q$ such that the Riccati polynomial candidate
corresponding to the invariant $p$ is $a^{-1} q$ if $a \ne 0$,
and $p$ does not absolutely factor linearly if $a = 0$, where
$a$ is the value of the invariant.}
#endif
			dualFirstIntegral: % -> V RF;
#if ASDOC
\aspage{dualFirstIntegral}
\Usage{\name~p}
\Signature{\%}{Vector Quotient Rx}
\Params{ {\em p} & \% & An invariant\\ }
\Retval{Returns the dual first integral corresponding to p.}
\seealso{polynomial(\this)}
#endif
			invariants: (Rxd, Z) -> List %;
			invariants: (EQ, Z) -> List %;
#if ASDOC
\aspage{invariants}
\Usage{\name(L, n)}
\Signatures{
\name: & (Rx, Integer) $\to$ List \%\\
\name: & (HolonomicEquation(R, Rx, Rxd), Integer) $\to$ List \%\\
}
\Params{
{\em L} & Rxd & A differential equation\\
        & HolonomicEquation(R, Rx, Rxd) & \\
{\em n} & Integer & A positive integer\\
}
\Retval{Returns a basis for the space of
homogeneous invariants of degree $n$ of $L$.}
\Remarks{The current implementation uses the cyclic vector method if $L$ has
exponents that are not rational numbers, a direct method otherwise.}
#endif
			polynomial: % -> V R;
#if ASDOC
\aspage{polynomial}
\Usage{\name~p}
\Signature{\%}{Vector R}
\Params{ {\em p} & \% & An invariant\\ }
\Retval{Returns a vector whose entries contains the
coordinates of the invariant in the basis
given by $\{{\tt lookup} 1,{\tt lookup} 2,\dots\}$ of
{\tt DenseHomogeneousPolynomial}(n,{\tt degree}(L)).
}
\seealso{dualFirstIntegral(\this)}
#endif
			value: % -> RF;
#if ASDOC
\aspage{value}
\Usage{\name~p}
\Signature{\%}{Quotient Rx}
\Params{ {\em p} & \% & An invariant\\ }
\Retval{Returns the value of the invariant for some basis of the
solution space.}
#endif
} == add {
	-- dfi = dual first integral (not multiplied by the multinomials)
	-- pol = invariant polynomial
	-- vl  = invariant value (coefficient of dfi in X_1^degree(pol))
	-- ric = corresponding Riccati candidate (X_1 -> Y, X_2 -> -1)
	macro Rep == Record(dfi:V RF, pol:V R, vl:I, ric:Py);
	import from Rep;

	local invariant(df:V RF, p:V R, v:I, r:Py):%	== per [df, p, v, r];
	dualFirstIntegral(p:%):V RF			== rep(p).dfi;
	polynomial(p:%):V R				== rep(p).pol;
	local val(p:%):I				== rep(p).vl;
	candidateRiccati(p:%):Py			== rep(p).ric;
	value(p:%):RF				== dualFirstIntegral(p).(val p);

	invariants(L:Rxd, m:Z):List % == {
		import from EQ;
		invariants(L::EQ, m);
	}

	invariants(L:EQ, m:Z):List % == {
		import from R, Rx, Rxd, DenseMatrix RF;
		import from DualFirstIntegral(R, Rx, Rxd);
		df := dualFirstIntegral(L, m);
		a := ordinaryPoint leadingCoefficient operator L;
		pow:I := retract m;
		ord:I := retract order L;
		(e, vl) := multinomialVector(ord, pow);
		[invariant!(column(df,c), a::R, e, vl, ord, pow)
							for c in 1..cols df];
	}

	-- m = order of the operator
	-- n = degree of the homogeneous invariants
	local multinomialVector(m:I, n:I):(V Z, I) == {
		import from DualFirstIntegralTools(R, Rx, n, m);
		v:V Z := zero(r := dimension);
		for i in 1..r repeat v.i := multinomial i;
		(v, value 1);
	}

	-- m = order of the operator
	-- n = degree of the homogeneous invariants
	-- may modify df
	local invariant!(df:V RF, a:R, e:V Z, vl:I, m:I, n:I):% == {
		import from Q, Rx, RF, Py, Array Py, V Q;
		import from VectorOverQuotient(R, Q);
		import from DualFirstIntegralTools(R, Rx, n, m);
		w:V Q := zero(r := #df);
		for i in 1..r repeat {
			f := df.i;
			w.i := e.i * (numerator(f)(a) / denominator(f)(a));
		}
		(c, v) := makeIntegral w;	-- v := c w
		if ~(one? c) then {
			cc := c::Rx;
			for i in 1..r repeat df.i := cc * df.i;
		}
		a:Array Py := new(m, 0);
		a.1 := monom;
		a.2 := -1;
		ev := eval(Py, a);
		riccati:Py := 0;
		for i in 1..r repeat
			riccati := add!(riccati, (e.i * df.i) * ev i);
		invariant(df, v, vl, riccati);
	}
}
