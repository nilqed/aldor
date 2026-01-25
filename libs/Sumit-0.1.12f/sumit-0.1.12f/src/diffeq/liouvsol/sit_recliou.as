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
------------------------------ sit_recliou.as ------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it ©INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I   == MachineInteger;
	Z   == Integer;
	V   == Vector;
	Rx  == Fraction RX;
	Fx  == Fraction FX;
}

#if ALDOC
\thistype{LinearOrdinaryRecurrenceLiouvillianSolutions}
\History{Manuel Bronstein}{24/8/2000}{created}
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
\Descr{\this(R, F, $\iota$, RX, RXE, FX) provides a Liouvillian solver
for linear ordinary recurrence operators with polynomial coefficients.}
\begin{exports}
\asexp{liouvillianSolution}:
& RXE $\to$ \astype{Vector} \astype{Fraction} FX &
A Liouvillian solution\\
\end{exports}
#endif

LinearOrdinaryRecurrenceLiouvillianSolutions(
	R:Join(GcdDomain, FactorizationRing), F:Field, inj: R -> F,
	RX: UnivariatePolynomialCategory R,
	RXE: LinearOrdinaryRecurrenceCategory RX,
	FX: UnivariatePolynomialCategory F): with {
		liouvillianSolution: RXE -> Vector Fx;
#if ALDOC
\aspage{liouvillianSolution}
\Usage{\name~L}
\Signature{RXE}{\astype{Vector} \astype{Fraction} FX}
\Params{
{\em L} & RXE & A linear ordinary recurrence operator\\
}
\Retval{Returns $[]$ if $L y = 0$ has no Liouvillian solution over $R$.
Otherwise, it returns $[f_1(n),\dots,f_m(n)]$
such that the interlacing of $y_1,\dots,y_m$ is a solution of $L y = 0$
where each $y_i$ is a solution of $y_i(n+1) = f_i(n) y_i(n)$.}
\Remarks{Note that \name~does not attempt to return several linearly
independent Liouvillian solutions, so if it finds one, there could
be some others. In addition, a return value of $[]$ proves that there
are no Liouvillian solutions over $R$, but there could be Liouvillian
solutions over the algebraic closure of its fraction field.}
#endif
} == add {
	liouvillianSolution(L:RXE):V Fx == {
		import from Boolean, I, Z;
		TRACE("recliou::liouvillianSolution: L = ", L);
		assert(~zero? L);
		L := primitivePart L;
		TRACE("recliou::liouvillianSolution: pp(L) = ", L);
		n := machine(degree L - trailingDegree L);
		zero? n => empty;
		for i in 1..n repeat {
			~empty?(v := tryInterlacing(L, i)) => return v;
		}
		empty;
	}

	local tryInterlacing(L:RXE, n:I):V Fx == {
		import from Z, Array RXE, Fx, Partial Fx,
			LinearOrdinaryRecurrenceHypergeometricSolutions(R, F,_
								inj, RX,RXE,FX);
		TRACE("recliou::tryInterlacing: L = ", L);
		TRACE("recliou::tryInterlacing: n = ", n);
		TIMESTART;
		a := sections(L, n::Z);
		TIME("recliou::tryInterlacing: sections at ");
		assert(n = #a);
		v:V Fx := zero n;
		for i in 0..prev n repeat {
			TRACE("recliou::tryInterlacing: i = ", i);
			TRACE("recliou::tryInterlacing: a.i = ", a.i);
			failed?(u:=hypergeometricSolution(a.i)) => return empty;
			v(next i) := retract u;
			TRACE("recliou::tryInterlacing: sol = ", v(next i));
		}
		v;
	}
}
