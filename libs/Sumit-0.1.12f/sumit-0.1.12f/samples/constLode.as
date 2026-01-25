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
------------------------------ constLode.as ------------------------------
--
-- This file contains a simple solver for homogeneous linear ordinary
-- differential equations with constant coefficients.
-- It demonstrates basic polynomial and operator manipulations
-- as well as printing a polynomial with a different symbol for variable
--
-- When compiled with '-fx -dMAKETEST', this crates a test executable
-- Otherwise, this creates a type usable in other Aldor programs.
--

#include "sumit"

macro Z == Integer;

-- The parameter R is for the constant coefficients of the equations
-- We ask that it has 'FactorizationRing' so that we can factor polynomials
-- over R. If factoring wasn't necessary, a weaker category would have been ok.
-- The parameter RX is to be used for returning the defining polynomials
-- of the algebraic numbers appearing in the result.
ConstantCoefficientLODOSolver(R:FactorizationRing,
	RX:UnivariatePolynomialCategory R,
	OP:LinearOrdinaryDifferentialOperatorCategory R): with {
	-- Returns a list of the form [(p1, n1), (p2, n2), ..., (pk, nk)]
	-- where the pk's are irreducible over R and each (p, n) yields the
	-- linearly independent solutions e^{ax},x e^{ax},...,x^{n-1} e^{ax}
	-- where a runs over all the roots of p(a) = 0.
	solve: OP -> List Cross(RX, Z);
} == add {
	solve(L:OP):List Cross(RX, Z) == {
		import from Boolean, Product RX;
		import from UnivariateFreeFiniteAlgebra2(R, OP, R, RX);

		-- we verify the validity of the input using an assertion
		-- so this verification disappears from optimized code (-q2)
		assert(~zero? L);

		-- the indicial equation of \sum_i a_i D^i is \sum_i a_i x^i
		-- so we simply use map$UnivariateFreeFiniteAlgebra2
		-- to lift the R -> R identity to a map R[D] -> R[x]
		indicialEquation:RX := map((r:R):R +-> r)(L);

		-- now we factor the indicial equation and return the pairs
		-- of irreducible factors and their exponents.
		(c, factors) := factor indicialEquation;

		-- the content 'c' can be ignored
		[pair for pair in factors];
	}
}

-- To make a test executable
#if MAKETEST
#include "sallio"		-- imports I/O stuff

macro {
	-- The variable in ZX will be printed as 'x'
	ZX == DenseUnivariatePolynomial(Z, -"x");

	-- The variable in ZD will be printed as 'D'
	-- The second parameter is actually 0-derivation from Derivation(Z)
	ZD == LinearOrdinaryDifferentialOperator(Z, 0, -"D");

	-- The arguments of the exponential can be rational numbers
	Q  == Fraction Z;
	QX == DenseUnivariatePolynomial(Q, -"x");
}

local testSolver():() == {
	import from Boolean, Symbol, Z, Q, ZX, Derivation Z;
	import from List Cross(ZX, Z), ConstantCoefficientLODOSolver(Z, ZX, ZD);

	stdout << "Enter a linear ordinary differential equation ";
	stdout << "with integer coefficients" << newline;
	stdout << "Use 'D' for the derivation and terminate with ';': "<< flush;
	L:ZD := << stdin;
	stdout << "A basis of solution of " << L << " is:" << newline;
	for pair in solve L repeat {
		(p, n) := pair;
		-- if p has degree 1, then we really solve p(a) = 0
		if degree(p) = 1 then {
			a := -coefficient(p, 0) / leadingCoefficient p;
			ax:QX := monomial(a, 1);
			for i in 0..prev n repeat {
				-- Use the fact that ZX prints its variable 'x'
				-- Only print '1' when it is a solution
				if i > 0 or zero? a then
					stdout << monomial(1, i)$ZX << " ";
				if ~zero? a then stdout << "e^{" << ax << "}";
				if i < prev n then stdout << ", ";
			}
		}
		-- otherwise we print its roots as 'a' and display 'p(a) = 0'
		else {
			for i in 0..prev n repeat {
				-- Never print '1' in this branch
				if i > 0 then stdout << monomial(1,i)$ZX << " ";
				stdout << "e^{a x}";
				if i < prev n then stdout << ", ";
			}
			stdout << " where ";
			-- 'stdout << p' would print the variable as 'x'
			-- so we use a different call to print it as 'a'
			stdout(p, -"a");
			stdout << " = 0";
		}
		stdout << newline;
	}
	stdout << endnl;
}

testSolver();
#endif
