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
------------------------------- binsearch.as ----------------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1995

#include "sumit"

#if ASDOC
\thistype{BinarySearch}
\History{Manuel Bronstein}{20/12/95}{created}
\Usage{import from \this(R, S)}
\Descr{\this(R, S) provides a general version of binary search.}
\Params{
{\em R} & Order & The space being searched\\
 & EuclideanDomain & \\
{\em S} & Order & The target values being searched for\\
}
\begin{exports}
binarySearch: & (S, R $\to$ S, R, R) $\to$ (Boolean, R) & Binary Search\\
\end{exports}
\begin{exports}[if S has OrderedAbelianGroup then]
binarySearch: & (S, S, R $\to$ S, R, R) $\to$ (Boolean, R) & Binary Search\\
\end{exports}
#endif

BinarySearch(R:Join(EuclideanDomain, Order), S:Order): with {
	binarySearch: (S, R -> S, R, R) -> (Boolean, R);
#if ASDOC
\aspage{binarySearch}
\Usage{\name(s, f, a, b)\\ \name(s, $\epsilon$, f, a, b) }
\Signatures{
\name: & (S, R $\to$ S, R, R) $\to$ (Boolean, R) \\
\name: & (S, S, R $\to$ S, R, R) $\to$ (Boolean, R) \\
}
\Params{
{\em s} & S & The value to search for\\
{\em $\epsilon$} & S & The tolerance on s ($\epsilon \ge 0$)\\
{\em f} & R $\to$ S & A monotonic increasing function\\
{\em a} & R & The left end of the interval to search\\
{\em b} & R & The right end of the interval to search\\
}
\Retval{\name(s, f, a, b) returns (found?, r) such that
$s = f(r)$ if found?~is \true. Otherwise, found?~is \false~and:
\begin{itemize}
\item ~if $r < a$ then $s < f(a)$;
\item ~if $r > b$ then $s > f(b)$;
\item ~if $r \in [a,b]$, then $f(r) < s < f(r')$,
where $r' = \min\{x \in R \st x > r\}$;
\end{itemize}
\name(s, $\epsilon$, f, a, b) returns (found?, r) such that
$f(r) - \epsilon \le s \le f(r) + \epsilon$ if found?~is \true.
Otherwise, found?~is \false~and:
\begin{itemize}
\item ~if $r < a$ then $s < f(a) - \epsilon$;
\item ~if $r > b$ then $s > f(b) + \epsilon$;
\item ~if $r \in [a,b]$, then $f(r) + \epsilon < s < f(r') - \epsilon$,
where $r' = \min\{x \in R \st x > r\}$;
\end{itemize}
}
#endif
	if S has OrderedAbelianGroup then
		binarySearch: (S, S, R -> S, R, R) -> (Boolean, R);
} == add {
	binarySearch(s:S, f:R -> S, a:R, b:R):(Boolean, R) == {
		TRACE("binarySearch: ", s);
		TRACE("left = ", a);
		TRACE("right = ", b);
		fa := f a; fb := f b;
		TRACE("f(left) = ", fa);
		TRACE("f(right) = ", fb);
		s < fa => (false, a - 1);
		s > fb => (false, b + 1);
		s = fa => (true, a);
		s = fb => (true, b);
		two:R := 1 + 1;
		while (m := (a + b) quo two) > a and m < b repeat {
			TRACE("median = ", m);
			fm := f m;
			TRACE("f(median) = ", fm);
			s = fm => return (true, m);
			if s < fm then b := m; else a := m;
		}
		(false, a);
	}

	if S has OrderedAbelianGroup then {
		close?(s:S, t:S, epsilon:S):Boolean == {
			x := s - t;
			x < epsilon and (-x) < epsilon;
		}

		binarySearch(s:S, epsilon:S, f:R->S, a:R, b:R):(Boolean,R) == {
			ASSERT(epsilon > 0);
			fa := f a; fb := f b;
			s < fa - epsilon => (false, a - 1);
			s > fb + epsilon => (false, b + 1);
			close?(s, fa, epsilon) => (true, a);
			close?(s, fb, epsilon) => (false, b);
			two:R := 1 + 1;
			while (m := (a + b) quo two) > a and m < b repeat {
				fm := f m;
				close?(s, fm, epsilon) => return (true, m);
				if s < fm - epsilon then b := m; else a := m;
			}
			(false, a);
		}
	}
}
