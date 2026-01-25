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
----------------------------- sit_ugring.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{UnivariateGcdRing}
\History{Manuel Bronstein}{20/9/95}{created}
\Usage{\this: Category}
\Descr{\this~is the category of rings which export a gcd algorithm for
univariate polynomials over themselves.}
\begin{exports}
\category{\astype{GcdDomain}}\\
\asexp{gcdUP}:
& (P:\astype{UnivariatePolynomialCategory0}) $\to$ (P, P) $\to$ P & Gcd\\
\asexp{gcdUP!}:
& (P:\astype{UnivariatePolynomialCategory0}) $\to$ (P, P) $\to$ P & Gcd\\
\asexp{gcdquoUP}:
& (P:\astype{UnivariatePolynomialCategory0}) $\to$ (P, P) $\to$ (P,P,P) & Gcd\\
\end{exports}
#endif

define UnivariateGcdRing: Category == GcdDomain with {
	gcdUP: (P: UnivariatePolynomialCategory0 %) -> (P, P) -> P;
	gcdUP!: (P: UnivariatePolynomialCategory0 %) -> (P, P) -> P;
#if ALDOC
\aspage{gcdUP}
\astarget{\name!}
\Usage{ \name(P)(p, q) \\ \name!(P)(p, q) }
\Signature{(P: \astype{UnivariatePolynomialCategory0} \%) $\to$ (P, P)}{P}
\Params{
{\em P} & \astype{UnivariatePolynomialCategory0} \% & A polynomial type\\
{\em p,q} & P & Polynomials\\
}
\Retval{Both function return $\gcd(p, q)$. When \name! is used, the
storage used by $x_1$ and $x_2$ is allowed to be destroyed or reused,
so $p$ and $q$ are lost after this call.}
#endif
	gcdquoUP: (P: UnivariatePolynomialCategory0 %) -> (P, P) -> (P, P, P);
#if ALDOC
\aspage{gcdquoUP}
\Usage{ \name(P)(p, q) }
\Signature{(P: \astype{UnivariatePolynomialCategory0} \%) $\to$ (P,P)}{(P,P,P)}
\Params{
{\em P} & \astype{UnivariatePolynomialCategory0} \% & A polynomial type\\
{\em p,q} & P & Polynomials\\
}
\Retval{Returns $(g, y, z)$ such that $g = \gcd(p, q)$, $p = g y$ and
$q = g z$.}
#endif
	default {
		gcdUP!(P: UnivariatePolynomialCategory0 %):(P,P) -> P == {
			(p:P, q:P):P +-> gcdUP(P)(p, q);
		}

		gcdquoUP(P: UnivariatePolynomialCategory0 %):(P,P)->(P,P,P) == {
			gcdP := gcdUP P;
			(p:P, q:P):(P, P, P) +-> {
				g := gcdP(p, q);
				(g, quotient(p, g), quotient(q, g));
			}
		}
	}
}

