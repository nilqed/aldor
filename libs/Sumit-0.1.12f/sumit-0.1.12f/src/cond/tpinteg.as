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
--------------------------- tpinteg.as ---------------------------
--
-- Test/demo of the parametric integration algorithm
--
-- Compile with axiomxl -fx -lsumit tpinteg.as psqfr.o pinteg.o
--
-- a is the parameter
-- x is the polynomial variable
-- discuss the sqrfree factorisation of p(a,x) based on conditions on a

#include "sumit"

#library param1 "psqfr.ao"
#library param2 "pinteg.ao"
import from param1, param2;
inline from param1, param2;

macro {
	Z == Integer;
	Q == Quotient Z;
	Qa == DenseUnivariatePolynomial(Q, "a");
	Qax == DenseUnivariatePolynomial(Qa, "x");
	F == Quotient Qax;
	COND == AlgebraicCondition(Q, "a");
	IR == IntegrationResult(Q, "a", Qax);
}

import from Z, Q, Qa, Qax, F, Pair(F,F), Case(COND, Pair(F,F)), Case(COND, IR);
import from ParametricUnivariateFractionIntegration(Q, "a", Qax);
a := monom$Qa :: Qax;
x := monom$Qax;

p := x * (x - 1) * (x - a);
f := inv(p::F);
print << "The integral of" << newline << f << newline;
-- print << "is " << hermiteCase f << newline;
print << "is " << intCase f << newline;

p := x * (x - 1)^2 * (x - a)^2;
f := inv(p::F);
print << "The integral of" << newline << f << newline;
-- print << "is " << hermiteCase f << newline;
print << "is " << intCase f << newline;
