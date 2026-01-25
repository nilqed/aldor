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
------------------------------ sit_sys1ser.as ------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I == MachineInteger;
	V == Vector;
	M == DenseMatrix;
	SYS == LinearOrdinaryFirstOrderSystem;
	RXD == LinearOrdinaryDifferentialOperator RX;
	RXE == LinearOrdinaryRecurrence(R, RX);
}

#if ALDOC
\thistype{LinearOrdinaryDifferentialSystemSeriesSolutions}
\History{Manuel Bronstein}{6/10/2000}{created}
\Usage{import from \this(R, F, $\iota$, RX, Fx)}
\Params{
{\em R} & \astype{IntegralDomain} & An integral domain\\
{\em F} & \astype{Field} & A field containing R\\
$\iota$ & $R \to F$ & Injection from R into F\\
{\em RX} & \astype{UnivariatePolynomialCategory} R & Polynomials over R\\
{\em Fx} & \astype{UnivariateTaylorSeriesCategory} F &
A series type over F\\
}
\Descr{\this(R, F, $\iota$, RX, Fx) provides a series solver
for linear ordinary differential systems with polynomial coefficients
around an ordinary point.}
\begin{exports}
\asexp{kernel}: & (SYS RX, R) $\to$ V V Fx & all the series solutions\\
\asexp{solution}:
& (SYS RX, R) $\to$ V F $\to$ V Fx $\to$ V Fx & solve an initial value problem\\
\end{exports}
\begin{aswhere}
SYS &==& \astype{LinearOrdinaryFirstOrderSystem}\\
V &==& \astype{Vector}\\
\end{aswhere}
#endif

LinearOrdinaryDifferentialSystemSeriesSolutions(R:IntegralDomain, F:Field,
		inj: R -> F,
		RX:UnivariatePolynomialCategory R,
		Fx:UnivariateTaylorSeriesCategory F): with {
			kernel: (SYS RX, R) -> V V Fx;
#if ALDOC
\aspage{kernel}
\Usage{\name(L, a)}
\Signature{(SYS RX, R)}{\astype{Vector} \astype{Vector} Fx}
\begin{aswhere}
SYS &==& \astype{LinearOrdinaryFirstOrderSystem}\\
\end{aswhere}
\Params{
{\em L} & SYS RX & A linear ordinary differential system\\
{\em a} & R & An ordinary point of L\\
}
\Retval{Returns a basis for the series solutions of $LY = 0$
around $x = a$.}
#endif
			solution: (SYS RX, R) -> V F -> V Fx -> V Fx;
#if ALDOC
\aspage{solution}
\Usage{\name(L, a)\\ \name(L, a)([$y_0,\dots,y_{m-1}$])\\
\name(L, a)([$y_0,\dots,y_{m-1}$])([$f_1,\dots,f_m$])}
\Signature{(SYS RX, R)}{\astype{Vector} \astype{Vector} F $\to$
\astype{Vector} Fx $\to$ \astype{Vector} Fx}
\begin{aswhere}
SYS &==& \astype{LinearOrdinaryFirstOrderSystem}\\
\end{aswhere}
\Params{
{\em L} & SYS RX & A linear ordinary differential system\\
{\em a} & R & An ordinary point of L\\
$y_i$ & F & Initial conditions\\
$f_i$ & Fx & A right-hand side\\
}
\Retval{\name(L, a)([$y_0,\dots,y_{n-1}$])([$f_1,\dots,f_m$])
returns the series solution of
$L Y = F$ around $x = a$
satisfying $Y_i(a) = y_i$ for $0 \le i < m$.}
#endif
} == add {
	local trans(a:R)(p:RX):RX		== translate(p, a);
	local series(n:I, s:Stream V F):V Fx	== [series(s, i) for i in 1..n];

	-- translate a to 0
	local translate(L:SYS RX, a:R):SYS RX == {
		import from RX, V RX, M RX;
		zero? a => L;
		ma := -a;
		(d, mat) := matrix L;
		system(map(trans ma)(d), map(trans ma)(mat));
	}

	kernel(L:SYS RX, a:R):V V Fx == {
		import from Boolean, I, Integer, F, V F;
		import from LinearOrdinaryRecurrenceSystemTools(R, F, inj, RX);
		import from LinearOrdinaryOperatorToRecurrence(R, RX, RXD, RXE);
		zero?(n := machine order L) => empty;
		L := translate(L, a);
		(RL, e) := recurrence L;
		-- If e > 0, then any vector of polynomials of degrees at
		-- most e-1 is also a solution
		-- Since there are n linearly independent solutions,
		-- this implies that e = 1 and that the solutions are
		-- all the constant vectors.
		e > 0 => {
			assert(one? e);
			[series(n, i) for i in 1..n];
		}
		k:Stream V V F := [kernel(RL, e)];
		[series(n, k, i) for i in 1..n];
	}

	local series(n:I, i:I):V Fx == {
		import from Fx;
		v := zero n;
		v.i := 1;
		v;
	}

	local series(n:I, k:Stream V V F, i:I):V Fx ==
		[series(k, i, j) for j in 1..n];

	local series(k:Stream V V F, i:I, j:I):Fx == {
		import from V F, V V F, Sequence F;
		series sequence([a.i.j for a in k]$Stream(F));
	}

	solution(L:SYS RX, a:R):V F -> V Fx -> V Fx == {
		import from Boolean, I, Integer, F, V F;
		import from LinearOrdinaryRecurrenceSystemTools(R, F, inj, RX);
		import from LinearOrdinaryOperatorToRecurrence(R, RX, RXD, RXE);
		L := translate(L, a);
		n := machine order L;
		assert(n > 0);
		solve:(V V F, Generator V F) -> Generator V F :=
							values recurrence L;
		(y:V F):V Fx -> V Fx +-> {
			z:V V F := [y];
			(rh:V Fx):V Fx +-> series(n,
					[solve(z,coefficients rh)]$Stream(V F));
		}
	}

	local coefficients(v:V Fx):Generator V F == generate {
		import from I, Fx, Generator F;
		n := #v;
		a:PrimitiveArray Generator F := new n;
		for i in 1..n repeat a(prev i) := coefficients(v.i);
		w:V F := zero n;
		repeat {
			for i in 1..n repeat w.i := next!(a(prev i));
			yield w;
		}
	}

	local series(k:Stream V F, i:I):Fx == {
		import from V F, Sequence F;
		series sequence([v.i for v in k]$Stream(F));
	}
}

