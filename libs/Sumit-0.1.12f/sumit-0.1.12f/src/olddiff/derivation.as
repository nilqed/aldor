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
------------------------------ derivation.as ----------------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1994

#include "sumit"

#if ASDOC
\thistype{Derivation}
\History{Manuel Bronstein}{21/12/94}{created}
\Usage{import from \this~R}
\Params{ {\em R} & Ring & The ring on which the derivations operate\\ }
\Descr{\this~R provides derivations on $R$.}
\begin{exports}
\category{AbelianGroup}\\
$\ast$: & (R, \%) $\to$ \% & Multiplication by a scalar\\
apply: & (\%, R, Integer) $\to$ R & Differentiate an element of $R$\\
derivation: & (R $\to$ R) $\to$ \% & Create a derivation\\
function: & \% $\to$ (R $\to$ R) & Action of a derivation\\
\end{exports}
#endif

Derivation(R:Ring): AbelianGroup with {
	*: (R, %) -> %;
#if ASDOC
\aspage{$\ast$}
\Usage{c \name~D}
\Signature{(R, \%)}{\%}
\Params{
{\em c} & R & A scalar\\
{\em D} & \% & A derivation\\
}
\Retval{Returns the derivation $c D$ defined by
$$
(c D) x = c (Dx)
$$
for any $x \in R$.}
#endif
	apply: (%, R, n:Integer == 1) -> R;
#if ASDOC
\aspage{apply}
\Usage{
\name(D, x)\\
\name(D, x, n)\\
D~x\\
D(x,n)
}
\Signature{(\%, R, .:Integer == 1)}{R}
\Params{
{\em D} & \% & A derivation\\ 
{\em x} & R & An element to differentiate\\
{\em n} & Integer & The number of times to differentiate (optional)\\
}
\Retval{Returns $D^n x$, \ie~the result of applying $D$ to $x$ $n$ times.}
#endif
	derivation: (R -> R) -> %;
#if ASDOC
\aspage{derivation}
\Usage{\name~f}
\Signature{(R $\to$ R)}{\%}
\Params{ {\em f} & R $\to$ R & A map\\ }
\Retval{Returns the derivation $D$ on $R$ given by
$$
D x = f(x)
$$
for any $x \in R$.}
\Remarks{$f$ must satisfy the rules of a derivation, namely:
$$
f(x+y) = f(x) + f(y),\quad\mbox{and}\quad
f(xy) = x f(y) + f(x) y
$$
for any $x, y \in R$.}
#endif
	function: % -> (R -> R);
#if ASDOC
\aspage{function}
\Usage{\name~D}
\Signature{\%}{(R $\to$ R)}
\Params{ {\em D} & \% & A derivation\\ }
\Retval{Returns the map corresponding to the action of $D$ on the ring.}
#endif
} == add {
	macro Rep == R -> R;

	0			== per((r:R):R +-> 0);
	sample:%		== 0;
	function(f:%):(R->R)	== rep f;
	-(f:%):%		== per((r:R):R +-> - (rep f) r);
	derivation(f:R -> R):%	== per f;
	(f:%) + (g:%):%		== per((r:R):R +-> (rep f)(r) + (rep g)(r));
	(p:TextWriter) << (x:%):TextWriter	== p;

	(u:%) = (v:%):Boolean == {
		import from Pointer;
		(u pretend Pointer) =$Pointer (v pretend Pointer);
	}

	apply(f:%, r:R, n:Integer):R == {
		ASSERT(n >= 0);
		g := function f;
		for i in 1..n repeat r := g r;
		r;
	}

	(c:R) * (f:%):% == {
		zero? c => 0;
		c = 1 => f;
		c = -1 => -f;
		per((r:R):R +-> c * (rep f) r);
	}
}
