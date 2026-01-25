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
------------------------------ sit_lodoser.as ------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I == MachineInteger;
	V == Vector;
	M == DenseMatrix;
	FX == DenseUnivariatePolynomial F;
	RXE == LinearOrdinaryRecurrence(R, RX);
}

#if ALDOC
\thistype{LinearOrdinaryDifferentialOperatorSeriesSolutions}
\History{Manuel Bronstein}{6/6/2000}{created}
\Usage{import from \this(R, F, $\iota$, RX, RXD, Fx)}
\Params{
{\em R} & \astype{IntegralDomain} & An integral domain\\
{\em F} & \astype{Field} & A field containing R\\
$\iota$ & $R \to F$ & Injection from R into F\\
{\em RX} & \astype{UnivariatePolynomialCategory} R & Polynomials over R\\
{\em RXD} & \astype{LinearOrdinaryDifferentialOperatorCategory} RX &
Differential operators\\
{\em Fx} & \astype{UnivariateTaylorSeriesCategory} F &
A series type over F\\
}
\Descr{\this(R, F, $\iota$, RX, RXD, Fx) provides a series solver
for linear ordinary differential operators with polynomial coefficients
around an ordinary point.}
\begin{exports}
\asexp{fundamentalMatrix}:
& (RXD, R) $\to$ \astype{DenseMatrix} Fx & fundamental solution matrix\\
\asexp{kernel}: & (RXD, R) $\to$ \astype{Vector} Fx & all the series solutions\\
\asexp{solution}: & (RXD, R) $\to$ \astype{Vector} F $\to$ Fx $\to$ Fx &
solve an initial value problem\\
\end{exports}
#endif

LinearOrdinaryDifferentialOperatorSeriesSolutions(R:IntegralDomain,
		F:Field, inj: R -> F,
		RX:UnivariatePolynomialCategory R,
		RXD:LinearOrdinaryDifferentialOperatorCategory RX,
		Fx:UnivariateTaylorSeriesCategory F): with {
			fundamentalMatrix: (RXD, R) -> M Fx;
#if ALDOC
\aspage{fundamentalMatrix}
\Usage{\name(L, a)}
\Signature{(RXD, R)}{\astype{DenseMatrix} Fx}
\Params{
{\em L} & RXD & A linear ordinary differential operator\\
{\em a} & R & An ordinary point of L\\
}
\Retval{Returns the matrix
$$
\pmatrix{
y_1  & \dots & y_n  \cr
y_1' & \dots & y_n' \cr
\vdots &        & \vdots \cr
y_1^{(n-1)} & \dots & y_n^{(n-1)} \cr
}
$$
where $(y_1,\dots,y_n)$ is a basis for the series solutions of $Ly = 0$
around $x = a$.}
#endif
			kernel: (RXD, R) -> V Fx;
#if ALDOC
\aspage{kernel}
\Usage{\name(L, a)}
\Signature{(RXD, R)}{\astype{Vector} Fx}
\Params{
{\em L} & RXD & A linear ordinary differential operator\\
{\em a} & R & An ordinary point of L\\
}
\Retval{Returns a basis for the series solutions of $Ly = 0$
around $x = a$.}
#endif
			solution: (RXD, R) -> V F -> Fx -> Fx;
#if ALDOC
\aspage{solution}
\Usage{\name(L, a)\\ \name(L, a)([$y_0,\dots,y_{m-1}$])\\
\name(L, a)([$y_0,\dots,y_{m-1}$])(f)}
\Signature{(RXD, R)}{\astype{Vector} F $\to$ Fx $\to$ Fx}
\Params{
{\em L} & RXD & A linear ordinary differential operator\\
{\em a} & R & An ordinary point of L\\
$y_i$ & F & Initial conditions\\
{\em f} & Fx & A right-hand side\\
}
\Retval{\name(L, a)([$y_0,\dots,y_{m-1}$])(f) returns the series solution of
$Ly = f$ around $x = a$
satisfying $y^{(i)}(a) = y_i$ for $0 \le i < m$.}
#endif
} == add {
	fundamentalMatrix(L:RXD, a:R):M Fx == map(differentiate$Fx) kernel(L,a);

	-- translate a to 0
	local translate(L:RXD, a:R):RXD == {
		import from RX;
		zero? a => L;
		ma := -a;
		map((p:RX):RX +-> translate(p, ma)) L;
	}

	solution(L:RXD, a:R):V F -> Fx -> Fx == {
		import from Boolean, I, Integer, RX, F, Sequence F;
		import from LinearOrdinaryRecurrenceTools(R, F, inj, RX, RXE);
		import from LinearOrdinaryOperatorToRecurrence(R, RX, RXD, RXE);
		assert(~zero? L);
		L := translate(L, a);
		n := machine degree L;
		assert(n > 0);
		assert(zero? trailingDegree leadingCoefficient L);
		solve:(V F, Generator F) -> Generator F := values recurrence L;
		(y:V F):Fx -> Fx +-> {
			assert(n = #y);
			-- convert initial values to Taylor series coefficients
			z:V F := zero n;
			z.1 := y.1;
			if n > 1 then {
				z.2 := y.2;
				m:Integer := 2;
				for i in 3..n repeat {
					z.i := y.i / (m::F);
					m := times!(m, i::Integer);
				}
			}
			(rh:Fx):Fx +-> series sequence(
					[solve(z, coefficients rh)]$Stream(F));
		}
	}

	kernel(L:RXD, a:R):V Fx == {
		import from Boolean, I, Integer, F, FX, Fx;
		assert(~zero? L);
		d := trailingDegree L;
		zero?(dd := machine d) => kernel0(L, a);
		k := kernel0(shift(L, -d), a);
		v:V Fx := zero(n := machine degree L);
		f := expand(FX, 0);
		for i in 1..dd repeat v.i := f(monomial(1, prev(i)::Integer));
		assert(#k = n - dd);
		for i in next(dd)..n repeat v.i := k(i - dd);
		v;
	}

	local kernel0(L:RXD, a:R):V Fx == {
		import from Boolean, I, Integer, F, RX, FX, Fx;
		import from LinearOrdinaryRecurrenceTools(R, F, inj, RX, RXE);
		import from LinearOrdinaryOperatorToRecurrence(R, RX, RXD, RXE);
		assert(~zero? L);
		assert(zero? trailingDegree L);
		zero?(n := machine degree L) => empty;
		L := translate(L, a);
		assert(zero? trailingDegree leadingCoefficient L);
		(RL, e) := recurrence L;
		-- Since L has trailing degree 0, its recurrence has the form
		-- (RL, e) where e <= 0, so we do not worry about e > 0 here
		k:Stream V F := [kernel recurrence L];
		[series(k, i) for i in 1..n];
	}

	local series(k:Stream V F, i:I):Fx == {
		import from V F, Sequence F;
		series sequence([v.i for v in k]$Stream(F));
	}
}

