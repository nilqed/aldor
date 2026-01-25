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
---------------------------- sal_bsearch.as -------------------------------
--
-- This file provides a fairly generic binary search for structures or int's.
--
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-1997
-- Copyright (c) Manuel Bronstein 1995-98
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

#if ALDOC
\thistype{BinarySearch}
\History{Manuel Bronstein}{20/12/95}{created}
\History{Manuel Bronstein}{28/9/98}{moved from sumit to salli and adapted}
\Usage{import from \this(R, S)}
\Descr{\this(R, S) provides a general version of binary search.}
\Params{
{\em R} & \astype{IntegerType} & The space being searched\\
{\em S} & \astype{TotallyOrderedType} & The target values being searched for\\
}
\begin{exports}
\asexp{binarySearch}: & (S, R $\to$ S, R, R) $\to$ (\astype{Boolean}, R) &
binary search\\
\end{exports}
#endif

BinarySearch(R:IntegerType, S:TotallyOrderedType): with {
	binarySearch: (S, R -> S, R, R) -> (Boolean, R);
#if ALDOC
\aspage{binarySearch}
\Usage{\name(s, f, a, b)}
\Signature{(S, R $\to$ S, R, R)}{(\astype{Boolean}, R)}
\Params{
{\em s} & S & The value to search for\\
{\em f} & R $\to$ S & A monotonic increasing function\\
{\em a} & R & The left end of the interval to search\\
{\em b} & R & The right end of the interval to search\\
}
\Retval{Returns (found?, r) such that
$s = f(r)$ if found?~is \true. Otherwise, found?~is \false~and:
\begin{itemize}
\item ~if $r < a$ then $s < f(a)$ or $b < a$;
\item ~if $r \ge b$ then $s > f(b)$;
\item ~if $a \le r < b$, then $f(r) < s < f(r+1)$;
\end{itemize}
}
#endif
} == add {
	binarySearch(s:S, f:R -> S, a:R, b:R):(Boolean, R) == {
		b < a or s < (fa := f a) => (false, prev a);
		fb := f b;
		two:R := 1 + 1;
		while fb < fa repeat {	-- only happens on overflow for f b
			b := (a + b) quo two;
			fb := f b;
		}
		s > fb => (false, b);
		s = fa => (true, a);
		s = fb => (true, b);
		while (m := (a + b) quo two) > a and m < b repeat {
			fm := f m;
			while fm < fa repeat {	-- overflow for f m
				m := (a + m) quo two;
				fm := f m;
			}
			s = fm => return (true, m);
			if s < fm then b := m; else a := m;
		}
		(false, a);
	}
}
