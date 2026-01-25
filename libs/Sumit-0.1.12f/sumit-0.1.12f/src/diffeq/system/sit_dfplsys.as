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
------------------------------ sit_dfplsys.as -------------------------------
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
	PRX == List Cross(RX, Z);
	Rx  == Fraction RX;
	SYS == LinearOrdinaryFirstOrderSystem;
	RXD == LinearOrdinaryDifferentialOperator RX;
	SOLVER == LinearOrdinaryFirstOrderSystemPolynomialSolutions(R,_
							F, inj, RX, RXD, FX);
}

#if ALDOC
\thistype{LinearOrdinaryDifferentialSystemPolynomialSolutions}
\History{Manuel Bronstein}{14/11/2000}{created}
\Usage{import from \this(R, F, $\iota$, RX, FX)}
\Params{
{\em R} & \astype{GcdDomain} & The coefficient ring\\
        & \astype{RationalRootRing} &\\
{\em F} & \astype{Field} & A field containing R\\
$\iota$ & $R \to F$ & Injection from R into F\\
{\em RX} & \astype{UnivariatePolynomialCategory} R & Polynomials over R\\
{\em FX} & \astype{UnivariatePolynomialCategory} F & Polynomials over F\\
}
\Descr{\this(R, F, $\iota$, RX, FX) provides a polynomial solver
for first order systems of linear ordinary differential operators
with polynomial coefficients.}
\begin{exports}
\asexp{degreeBound}: & SYS RX $\to$ \astype{Integer} & Degree bound\\
\asexp{kernel}: & SYS RX $\to$ \astype{DenseMatrix} FX & Polynomial solutions\\
\end{exports}
\begin{aswhere}
SYS &==& \astype{LinearOrdinaryFirstOrderSystem}\\
\end{aswhere}
#endif

LinearOrdinaryDifferentialSystemPolynomialSolutions(
	R:Join(GcdDomain, RationalRootRing),
	F:Field, inj: R -> F,
	RX: UnivariatePolynomialCategory R,
	FX: UnivariatePolynomialCategory F): with {
		degreeBound: SYS RX -> Z;
#if ALDOC
\aspage{degreeBound}
\Usage{\name~L}
\Signature{\astype{LinearOrdinaryFirstOrderSystem} RX}{\astype{Integer}}
\Params{
{\em L} & \astype{LinearOrdinaryFirstOrderSystem} RX &
A first order differential system\\
}
\Retval{Returns an upper bound for the degree of any polynomial solution
of $LY = 0$, $-1$ if there are no nonzero polynomial solution.}
#endif
		kernel: SYS RX -> M FX;
#if ALDOC
\aspage{kernel}
\Usage{\name~L}
\Signature{\astype{LinearOrdinaryFirstOrderSystem} RX}{\astype{DenseMatrix} FX}
\Params{
{\em L} & \astype{LinearOrdinaryFirstOrderSystem} RX &
A first order differential system\\
}
\Retval{Returns a basis for all the polynomial solutions of $LY = 0$.}
#endif
} == add {
	-- returns an equation for the degree of the polynomial solutions
	-- if the system if simple at infinity, failed otherwise
	local indicialEquation(L:SYS RX):Partial RX == failed;

	degreeBound(L:SYS RX):Z == {
		import from I, Partial Z, RX, Partial RX;
		failed?(u := indicialEquation L) => degreeBound(L)$SOLVER;
		TRACE("dfplsys::degreeBound: indicial equation = ", retract u);
		failed?(v := maxIntegerRoot retract u) => -1;
		TRACE("dfplsys::degreeBound: degree bound = ", retract v);
		retract v;
	}

	kernel(L:SYS RX):M FX == {
		import from I, Z, Partial Z, RX, Partial RX;
		failed?(u := indicialEquation L) => kernel(L)$SOLVER;
		TRACE("dfplsys::kernel: indicial equation = ", retract u);
		failed?(v := maxIntegerRoot retract u) =>
			zero(machine order L, 0);
		TRACE("dfplsys::kernel: degree bound = ", retract v);
		kernel(L, retract v)$SOLVER;
	}
}

