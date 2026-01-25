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
------------------------------- sit_intdom.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{IntegralDomain}
\History{Manuel Bronstein}{21/11/94}{created}
\History{Manuel Bronstein}{24/09/96}{added order}
\Usage{\this: Category}
\Descr{\this~is the category of commutative integral domains.}
\begin{exports}
\category{\astype{CommutativeRing}}\\
\asexp{order}: & \% $\to$  \% $\to$ \astype{Integer} & Order of divisibility\\
\asexp{orderquo}: & \% $\to$  \% $\to$ (\astype{Integer}, \%) &
Order of divisibility and quotient\\
\end{exports}
#endif

define IntegralDomain: Category == CommutativeRing with {
	order: % -> % -> Integer;
#if ALDOC
\aspage{order}
\Usage{\name~a\\ \name(a)(b)}
\Signature{\% $\to$ \%}{\astype{Integer}}
\Params{
{\em a} & \% & A nonunit element of the domain\\
{\em b} & \% & A nonzero element of the domain\\
}
\Retval{\name(a)(b) returns the unique nonnegative integer $n = \nu_a(b)$
such that $a^n \mid b$ and $a^{n+1} \nodiv b$, while \name(a) returns the map
$b \to \nu_a(b)$.}
\Remarks{\name(a) makes some precalculations based on a, so if you need to
use \name(a)(b) several times with the same a and different b's, it is
more efficient to compute \name(a) once and assign it, as in the example
below. In addition, if you need to compute $b / a^{\nu_a(b)}$, then it
is more efficient to use the {\tt orderquo} function.}
\begin{asex}
The following function computes the orders at $x^2 + 1$ of
a list of polynomials $l := [p_1,\dots,p_n]$:
\begin{ttyout}
orders(l:List DenseUnivariatePolynomial Integer):List Integer == {
    import from DenseUnivariatePolynomial Integer;
    nu := order(monom * monom + 1);    -- order function at x^2 + 1
    [nu(p) for p in l];
}
\end{ttyout}
\end{asex}
\seealso{\asexp{orderquo}}
#endif
	orderquo: % -> % -> (Integer, %);
#if ALDOC
\aspage{orderquo}
\Usage{\name~a\\ (n, c) := \name(a)(b);}
\Signature{\% $\to$ \%}{(\astype{Integer}, \%)}
\Params{
{\em a} & \% & A nonunit element of the domain\\
{\em b} & \% & A nonzero element of the domain\\
}
\Retval{\name(a)(b) returns $(n, c)$ such that $b = c a^n$ and $a \nodiv c$,
while \name(a) returns the map $b \to$~\name(a)(b).}
\Remarks{\name(a) makes some precalculations based on a, so if you need to
use \name(a)(b) several times with the same a and different b's, it is
more efficient to compute \name(a) once and assign it.}
\seealso{\asexp{order}}
#endif
	default {
		order(a:%)(b:%):Integer == {
			(n, c) := orderquo(a)(b);
			n;
		}

		orderquo(a:%)(b:%):(Integer, %) == {
			import from Boolean, Partial %;
			assert(~zero? a and ~zero? b and ~unit? a);
			n:Integer := 0;
			while ~failed?(u := exactQuotient(b, a)) repeat {
				n := next n; b := retract u;
			}
			(n, b);
		}
	}
}
