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
------------------------- heugcd.as ----------------------------
#include "sumit"

#if ASDOC
\thistype{HeuristicGcd}
\History{Manuel Bronstein}{13/8/94}{created}
\Usage{import from \this(Z, P)}
\Params{
{\em Z} & IntegerCategory & An integer-like ring\\
{\em P} & UnivariatePolynomialCategory0 Z & Polynomials over Z\\
}
\Descr{\this~provides an implementation of the HEUGCD algorithm for
univariate polynomials over the integers.}
\begin{exports}
balancedRemainder: & (Z, Z) $\to$ Z & Symmetric Remainder\\
heuristicGcd: & (P, P) $\to$ (Partial P, P, P) &
the Heuristic gcd algorithm\\
radixInterpolate: & (Z, Z) $\to$ P & Radix interpolation\\
\end{exports}
#endif

HeuristicGcd(Z:IntegerCategory, P:UnivariatePolynomialCategory0 Z): with {
		balancedRemainder: (Z, Z) -> Z;
#if ASDOC
\begin{aspage}{balancedRemainder}
\Usage{\name(n, m)}
\Signature{(Z, Z)}{Z}
\Params{
{\em n} & Z & An integer\\
{\em m} & Z & An integer\\
}
\Retval{Returns $-m/2 \le r < m/2$ such that $n \equiv r \pmod m$.}
\end{aspage}
#endif
		heuristicGcd: (P, P) -> (Partial P, P, P);
#if ASDOC
\begin{aspage}{heuristicGcd}
\Usage{\name($p_1, p_2$)}
\Signature{(P, P)}{(Partial P, P, P)}
\Params{ {\em $p_1, p_2$} & P & Polynomials\\ }
\Retval{Returns $(g, q_1, q_2)$ such that $g = \gcd(p_1, p_2)$,
$p_1 = g q_1$ and $p_2 = g q_2$.}
\Remarks{This heuristic can fail in theory, in which case
(\failed, $p_1, p_2$) is returned, although this has never been reported.}
\end{aspage}
#endif
		radixInterpolate: (Z, Z) -> P;
#if ASDOC
\begin{aspage}{radixInterpolate}
\Usage{\name(n, m)}
\Signature{(Z, Z)}{P}
\Params{
{\em n} & Z & A point\\
{\em m} & R & The value of the desired polynomial at n\\
}
\Retval{Returns the unique polynomial $p$ such that $p(n) = m$ and
$$
\vert\vert p \vert\vert_\infty \le \frac{n - 1}2\,.
$$
}
\Remarks{The above bound is useful when an upper bound $M$
on $\vert\vert p \vert\vert_\infty$ is known a priori,
since it is then sufficient to take $n \ge 2 M + 1$.}
\end{aspage}
#endif
} == add {
	-- From Zippel, "Effective Polynomial Computation",
	-- sec. 15.1 on HeuristicGCD
	heuristicGcd(p:P, q:P):(Partial P, P, P) == {
		import from Integer, Z, Partial P, RandomNumberGenerator;
		zero? p => ([q], 0, 1); zero? q => ([p], 1, 0);
		START__TIME;
		d := next min(degree p, degree q);
		(cp, p) := primitive p; (cq, q) := primitive q;
		bound := (d * 2^d)::Z * max(height p, height q);
		for i in 1..100@Integer repeat {
			e := bound + randomInteger()::Z;
			h := primitivePart radixInterpolate(e, gcd(p e, q e));
			~failed?(pquo := exactQuotient(p, h)) and
				~failed?(qquo := exactQuotient(q, h)) => {
					(g, cp, cq) := gcdquo(cp, cq);
					TIME("heuristicGcd:success at ");
					return([times!(g, h)],
						times!(cp, retract pquo),
						times!(cq, retract qquo));
			}
		}
		TIME("heuristicGcd:failure at ");
		(failed, p, q);
	}

	balancedRemainder(a:Z, b:Z):Z == {
		ASSERT(b > 0);
		r := a rem b;
		r < b quo 2 => r;
		r - b;
	}

	-- From Zippel, "Effective Polynomial Computation",
	-- sec. 15.1 on HeuristicGCD
	radixInterpolate(point:Z, image:Z):P == {
		ASSERT(point > 0);
		p:P := 0;
		d:Integer := 0;
		while image ~= 0 repeat {
			h := balancedRemainder(image, point);
			p := add!(p, h, d);
			image := (image - h) quo point;
			d := next d;
		}
		p;
	}
}
