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
------------------------------- qfactor.as --------------------------------
#include "sumit"

macro {
	Q	== Quotient Z;
	PZ	== DenseUnivariatePolynomial Z;
	FR	== Record(lcoeff:Q,factors:Product P);
}

#if ASDOC
\thistype{UnivariateRationalFactorizer}
\History{Laurent Bernardin}{4/12/95}{created}
\Usage{import from \this(Z, P);}
\Params{
{\em Z} & IntegerCategory & An integer-like ring\\
{\em P} & UnivariatePolynomialCategory0 Quotient Z &
A polynomial type over Quotient Z\\
}
\Descr{\this(Z, P) implements a factorizer for polynomials with
rational coefficients.}
\begin{exports}
factor: & P $\to$ Record(lcoeff:Quotient Z,factors:Product P) & Factor\\
\end{exports}
#endif

UnivariateRationalFactorizer(Z:IntegerCategory,
				P:UnivariatePolynomialCategory0 Q): with {
	factor:			P	->	FR;
#if ASDOC
\aspage{factor}
\Usage{\name~p}
\Signature{P}{Record(lcoeff:Quotient Z,factors:Product P)}
\Params{ {\em p} & P & A polynomial with rational coefficients\\ }
\Retval{Returns $(c, p_1^{e_1} \cdots p_n^{e_n})$ such that
each $p_i$ is irreducible, the $p_i$'s have no common factors, and
$$
p = c\;\prod_{i=1}^n p_i^{e_i}\,.
$$
}
\seealso{squareFree(UnivariatePolynomialCategory0)}
#endif
} == add {
	import from UnivariateIntegralFactorizer(Z, PZ), _
			UnivariateFreeAlgebraOverQuotient(Z, PZ, Q, P);

	factor(f:P):FR == {
		import from Integer, Q, Product P;
		import from Record(lcoeff:Z, factors:Product PZ);
		(m, p) := makeIntegral f;
		fr := factor p;
		(c, q) := normalize(fr.factors);
		[c * fr.lcoeff / m, q];
	}

	-- returns (c, q) s.t. p = c q
	local normalize(p:Product PZ):(Z, Product P) == {
		c:Z := 1;
		q:Product P := 1;
		for term in p repeat {
			(r, e) := term;			-- factor is r^e
			(a, s) := normalize r;		-- r = a s, s monic
			q := times!(q, s, e);
			c := times!(c, a^e);
		}
		(c, q);
	}
}

