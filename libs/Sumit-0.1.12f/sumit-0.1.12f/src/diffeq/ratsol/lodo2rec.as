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
------------------------------ lodo2rec.as ------------------------------
#include "sumit"

macro {
	Z  == Integer;
	Re == LinearOrdinaryDifferenceOperator(R, Rx);
	HR == HolonomicRecurrence(R, Rx);
}

#if ASDOC
\thistype{LinearOrdinaryDifferentialToDifferenceOperator}
\History{Manuel Bronstein}{3/11/97}{created}
\Usage{ import from \this(R, Rx, Rxd);}
\Params{
{\em R} & CommutativeRing & A commutative ring\\
{\em Rx} & UnivariatePolynomialCategory R & A polynomial ring over R\\
{\em Rxd} & LinearOrdinaryDifferentialOperatorCategory Rx &
A ring of operators over Rx\\
}
\Descr{\this(R, Rx, Rxd) provides conversions from differential operators
to recurrences.}
\begin{exports}
recurrence: & Rxd $\to$ HolonomicRecurrence(R, Rx) & recurrence at 0\\
\end{exports}
#endif

LinearOrdinaryDifferentialOperatorToDifferenceOperator(R:CommutativeRing,
	Rx:UnivariatePolynomialCategory R,
	Rxd:LinearOrdinaryDifferentialOperatorCategory Rx): with {
		recurrence: Rxd -> HR;
#if ASDOC
\aspage{recurrence}
\Usage{\name~L}
\Signature{Rxd}{HolonomicRecurrence(R, Rx)}
\Params{ {\em L} & Rxd & A differential operator\\ }
\Retval{Returns $(\sum_i a_i E^i, m)$ such that for any formal series
solution $\sum_{n >= 0} a_n x^n$ of $L y = 0$, the sequence $(a_0,a_1,\dots)$
is a solution of
$$
\paren{\sum_i a_i E^{i+m}} y = 0\,.
$$
}
#endif
	} == add {
		-- Computes the integer b and the operator p(L) such that
		--       R(L) = p(L) E^b
		-- where R(L) is the recurrence corresponding to L at x=0 as in:
		-- S.A.Abramov, "Solutions of linear differential equations in
		-- the class of sparse power series", Proceedings of FPSAC'97
		-- The closed form formulas for b and p(L) are:
		--   b    = min_j(j - deg_x(p_j))
		--   p(L) = \sum_j \sum_i a_i (n + 1 - i)^{\bar j} E^{j - i - b}
		-- where x^{\bar j} is the ascending Pochammer of degree j
		-- and   L = \sum_j (\sum_i a_i x^i) D^j
		recurrence(L:Rxd):HR == {
			import from Z, Rx;
			b := minOrder L;
			r:Re := 0;
			for term in L repeat {
				(p, j) := term;
				for pterm in p repeat {
					(a, i) := pterm;
					r := add!(r, a * poch(1-i, j), j-i-b);
				}
			}
			shift(r, b);
		}

		-- returns (x+a)(x+a+1)...(x+a+(n-1))
		local poch(a:Z, n:Z):Rx == {
			p:Rx := 1;
			x:Rx := monom;
			for i in 1..n repeat p := times!(p, x + (a+prev i)::Rx);
			p;
		}

		-- returns min(n - deg(coeff(L,n),x)) over the coeffs of L
		local minOrder(L:Rxd):Z == {
			import from Rx;
			b := degree L - degree leadingCoefficient L;
			for term in reductum L repeat {
				(p, n) := term;
				m := n - degree p;
				if m < b then b := m;
			}
			b;
		}
}
