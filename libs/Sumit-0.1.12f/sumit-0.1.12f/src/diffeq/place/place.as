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
------------------------------ place.as --------------------
#include "sumit"

macro {
	Z  == Integer;
	RR == RationalRoot;
	POLY == UnivariatePolynomialCategory;
}

#if ASDOC
\thistype{Place}
\History{Manuel Bronstein}{31/1/95}{created}
\Usage{\this(R, F): Category}
\Params{
{\em R} & Ring & The coefficient ring of the place\\
{\em F} & SumitRing & The residue ring at the place\\
}
\Descr{\this(R, F) is the category of potential localisations of the elements
of R (typically polynomials, fractions or series).
Each element of R can be uniquely represented as a Laurent series in some
local uniformizer at a place, with coefficients in F. The uniformizer does
not always belong to R or F.}
\begin{exports}
degree: & $\to$ Z & number of points represented\\
leadingCoefficient: & R $\to$ F & leading coefficient at the place\\
multiplicity: & (RR, P:POL Residue) $\to$ P $\to$ Integer &
multiplicity of a root\\
orderOf: & (R, Z) $\to$ Partial Z & bounded order at the place\\
orderOf: & R $\to$ Z & order at the place\\
value: & R $\to$ F & value at the place\\
\end{exports}
\begin{aswhere}
Z &==& Integer\\
RR &==& RationalRoot\\
POL &==& UnivariatePolynomialCategory\\
\end{aswhere}
#endif

Place(R:Ring, Residue:SumitRing): Category == with {
	degree: Z;
#if ASDOC
\aspage{degree}
\Usage{\name}
\Signature{}{Integer}
\Retval{Returns the number of points actually represented by the place.}
#endif
	leadingCoefficient: R -> Residue;
#if ASDOC
\aspage{leadingCoefficient}
\Usage{\name~f}
\Signature{R}{F}
\Params{ {\em f} & R & An element of the coefficient ring.\\ }
\Retval{Returns the leading coefficient of the series expansion of $f$
at the place, \ie~$a\in F^\ast$ where
$$
f = a t^m + \sum_{i > m} a_i t^i\,.
$$
}
\Remarks{This function needs to compute $\nu(f)$, so if $R$ does not provide an
effective zero-test, it should be used only when $f$ is known to be nonzero.}
\seealso{orderOf(\this), value(\this)}
#endif
	multiplicity: (RationalRoot, P:POLY Residue) -> P -> Z;
#if ASDOC
\aspage{multiplicity}
\Usage{\name(r, P, p)}
\Signature{(RationalRoot, P:UnivariatePolynomialCategory Residue)}
{P $\to$ Integer}
\Params{
{\em r} & RationalRoot & A rational root of p\\
{\em P} & UnivariatePolynomialCategory Residue, & A polynomial type\\
{\em p} & P & A polynomial\\
}
\Retval{Returns the number of times that the root rt appears at all
the points represented by the place.}
#endif
	orderOf: (R, Z) -> Partial Z;
	orderOf: R -> Z;
#if ASDOC
\aspage{orderOf}
\Usage{ \name~f\\ \name~(f, m)\\ }
\Signatures{
\name: & R $\to$ Integer\\
\name: & (R, Integer) $\to$ Partial Integer\\
}
\Params{
{\em f} & R & An element of the coefficient ring.\\
{\em m} & Integer & An upper bound\\
}
\Retval{
\name~f returns $\nu(f)$, the order of $f$ at the place, \ie~$n$ where
$$
f = a t^n + \sum_{i > n} a_i t^i
$$
and $a \ne 0$.\\
\name(f, m) returns $\nu(f)$ if $\nu(f) \le m$, \failed~otherwise.}
\Remarks{\name~f should be used only when $f$ is known to be nonzero,
while \name(f, m) can be always be used, even if $f = 0$ or if $R$ does
not provide an effective zero test.}
\seealso{leadingCoefficient(\this), value(\this)}
#endif
	value: R -> Residue;
#if ASDOC
\aspage{value}
\Usage{\name~f}
\Signature{R}{F}
\Params{ {\em f} & R & An element of the coefficient ring.\\ }
\Retval{Returns the value of $f$ at the place, which is defined to be the
leading coefficient of $f$ if $\nu(f) = 0$ and $0$ if $\nu(f) > 0$.}
\Remarks{This function does not need to test whether $f = 0$, so it can
be used even if $R$ does not provide an effective zero test. On the other
hand, one must have $\nu(f) \ge 0$.}
\seealso{leadingCoefficient(\this), orderOf(\this)}
#endif
	default {
		degree:Z == 1;
		multiplicity(r:RR, P:POLY Residue):P -> Z == {
			(p:P):Z +-> multiplicity r;
		}
	}
}
