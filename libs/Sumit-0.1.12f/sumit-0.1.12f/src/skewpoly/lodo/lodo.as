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
------------------------------ lodo.as ------------------------------
#include "sumit"

#if ASDOC
\thistype{LinearOrdinaryDifferentialOperator}
\History{Manuel Bronstein}{21/12/94}{created}
\Usage{
import from \this~R;\\
import from \this(R, x);\\
import from \this(R, D);\\
import from \this(R, D, x);
}
\Params{
{\em R} & CommutativeRing & The coefficient ring of the operators\\
& DifferentialRing & \\
{\em D} & Derivation R & The derivation on R to use for the action\\
{\em x} & String & The variable name (optional)\\
}
\Descr{\this(R, D, x) implements linear ordinary differential
operators with coefficients in R. If the derivation D is not specified,
then R must be a DifferentialRing. It is possible to override the
default derivation on R simply by passing another one as parameter.}
\begin{exports}
\category{LinearOrdinaryDifferentialOperatorCategory R}\\
\end{exports}
#endif

macro {
	Symbol	== String;
	anon	== "\partial";
	SP	== SymmetricPower(R pretend IntegralDomain, %, n, m);
}

LinearOrdinaryDifferentialOperator(R:CommutativeRing, D: Derivation R,
	avar:Symbol == anon): LinearOrdinaryDifferentialOperatorCategory R == {

	import from Automorphism R;

	DenseUnivariateSkewPolynomial(R, 1, function D, avar) add {
		apply(p:%, r:R):R	== apply(p, 0, r);
		derivation:Derivation R	== D;

		-- TEMPORARY: DEFAULT NOT FOUND OTHERWISE
		local pm1(n:Integer):R == { odd? n => - 1; 1 };

		adjoint(l:%):% == {
			import from R;
			a:% := 0;
			for term in l repeat {
				(c, n) := term;
				a := add!(a, pm1 n, monomial(1, n) * (c::%));
			}
			a;
		}
	}
}


LinearOrdinaryDifferentialOperator(R:DifferentialRing,
	avar:Symbol == anon): LinearOrdinaryDifferentialOperatorCategory R ==
-- TEMPORARY: NO CONDITIONAL CONSTANTS (969)
-- LinearOrdinaryDifferentialOperator(R, derivation$R, avar);
		LinearOrdinaryDifferentialOperator(R, derivation()$R, avar);

#if SUMITTEST
---------------------- test lodo.as --------------------------
#include "sumittest.as"

macro {
	Z == Integer;
	Zx == SparseUnivariatePolynomial(Z, "x");
	Fd == LinearOrdinaryDifferentialOperator(Zx, "D");
}

degree():Boolean == {
	import from Z, Zx, Fd;
	x:Zx := monomial(1, 1);
	dx:Fd := monomial(1, 1);
	p := x^2 * dx^2 - x * dx + 1;
	degree p = 2 and leadingCoefficient p = x*x
			and zero?(x + leadingCoefficient reductum p);
}

exactQuotient():Boolean == {
	import from Z, Zx, Fd, Partial Fd;

	x:Zx := monomial(1, 1);
	dx:Fd := monomial(1, 1);
	p := dx * dx - x::Fd;			-- p = D^2 - x  (Airy)
	p2 := p * p;
	ap2 := adjoint p2;			-- p and p^2 are self-adjoint
	ql := leftExactQuotient(ap2, p);	-- must be p
	qr := rightExactQuotient(p2, p);	-- must be p
	~(failed? ql) and ~(failed? qr) and retract(ql) = p and retract(qr) = p;
}

print << "Testing lodo..." << newline;
sumitTest("degree", degree);
sumitTest("exactQuotient", exactQuotient);
print << newline;
#endif

