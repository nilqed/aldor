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
-------------------------- sit_pfunc.as ---------------------------------
--
-- Partial functions, i.e. functions that are allowed to fail on some inputs
--
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "salli"

#if ALDOC
\thistype{PartialFunction}
\History{Manuel Bronstein}{23/6/95}{created}
\Usage{import from \this(R, S)}
\Params{
{\em R} & \builtin{Type} & Contains the domain of the function\\
{\em S} & \builtin{Type} & Contains the image of the function\\
}
\Descr{ \this~provides partial functions from R to S, \ie functions
from R to S which are allowed to fail on some elements of R.}
\begin{exports}
\asexp{apply}: & (\%, R) $\to$ S & Apply a partial function\\
\asexp{inDomain?}:
& (\%, R) $\to$ \astype{Boolean} & Check if an element is in the domain\\
\asexp{mapping}: & \% $\to$ (R $\to$ S) & Action of a function\\
\asexp{partialApply}:
& (\%, R) $\to$ \astype{Partial} S & Apply a partial function\\
\asexp{partialMapping}:
& \% $\to$ (R $\to$ \astype{Partial} S) & Action of a function\\
\asexp{predicate}:
& \% $\to$ (R $\to$ \astype{Boolean}) & Domain of a partial function\\
\asexp{partialFunction}:
& (R $\to$ \astype{Partial} S) $\to$ \% & Create a partial function\\
\asexp{partialFunction}: & ((R $\to$ \astype{Boolean}, R $\to$ S)) $\to$ \% &
Create a partial function\\
\end{exports}
#endif

PartialFunction(R:Type, S:Type): with {
	apply: (%, R) -> S;
#if ALDOC
\aspage{apply}
\Usage{ \name($\sigma$, x) \\ $\sigma x$}
\Signature{(\%, R)}{S}
\Params{
{\em $\sigma$} & \% & A partial function\\
{\em x} & R & An element of R\\
}
\Retval{Returns $\sigma x$.}
\Remarks{This map can cause an error if it is used on an element which is
not in the domain of $\sigma$. Use only when x is known to be in the domain,
otherwise use {\em partialApply}.}
\seealso{\asexp{inDomain?}, \asexp{predicate}, \asexp{partialApply}}
#endif
	inDomain?: (%, R) -> Boolean;
#if ALDOC
\aspage{inDomain?}
\Usage{ \name~x }
\Signature{(\%, R)}{\astype{Boolean}}
\Params{
{\em $\sigma$} & \% & A partial function\\
{\em x} & R & An element of R\\
}
\Retval{Returns \true~if x is in the domain of $\sigma$, \false otherwise.}
\seealso{\asexp{predicate}}
#endif
	mapping: % -> (R -> S);
#if ALDOC
\aspage{mapping}
\Usage{\name~$\sigma$}
\Signature{\%}{(R $\to$ S)}
\Params{ {\em $\sigma$} & \% & A partial function\\ }
\Retval{Returns the map corresponding to the action of $\sigma$ on R.}
\Remarks{The map returned can cause an error if it is used on an element which
is not in the domain of $\sigma$. Use only when x is known to be in the domain,
otherwise use {\em partialMapping}.}
\seealso{\asexp{inDomain?}, \asexp{partialMapping}, \asexp{predicate}}
#endif
	partialMapping: % -> (R -> Partial S);
#if ALDOC
\aspage{partialMapping}
\Usage{\name~$\sigma$}
\Signature{\%}{(R $\to$ \astype{Partial} S)}
\Params{ {\em $\sigma$} & \% & A partial function\\ }
\Retval{Returns the map corresponding to the action of $\sigma$ on R.}
\seealso{\asexp{inDomain?}, \asexp{mapping}, \asexp{predicate}}
#endif
	predicate: % -> (R -> Boolean);
#if ALDOC
\aspage{predicate}
\Usage{\name~$\sigma$}
\Signature{\%}{(R $\to$ \astype{Boolean}}
\Params{ {\em $\sigma$} & \% & A partial function\\ }
\Retval{Returns the predicate defining the domain of $\sigma$.}
\seealso{\asexp{inDomain?}}
#endif
	partialFunction: (R -> Partial S) -> %;
	partialFunction: (R -> Boolean, R -> S) -> %;
#if ALDOC
\aspage{partialFunction}
\Usage{\name~f\\ \name(p, g)}
\Signatures{
\name: & (R $\to$ \astype{Partial} S) $\to$ \%\\
\name: & (R $\to$ \astype{Boolean}, R $\to$ S) $\to$ \%\\
}
\Params{
{\em f} & R $\to$ \astype{Partial} S & A partial map\\
{\em p} & R $\to$ \astype{Boolean} & A predicate\\
{\em g} & R $\to$ S & A map\\
}
\Retval{\name(f) returns the partial function $\sigma$ on $R$ given by
$$
\sigma x = f(x)
$$
for any $x \in R$, while \name(p, g) returns the partial function $\sigma$ on $R$ given by
$$
\sigma x = \left\{ \begin{array}{ll}
g(x) & if p(x) = \true\\
\failed & if p(x) = \false\\ \end{array} \right.
$$
}
#endif
	partialApply: (%, R) -> Partial S;
#if ALDOC
\aspage{partialApply}
\Usage{ \name~x }
\Signature{(\%, R)}{\astype{Partial} S}
\Params{
{\em $\sigma$} & \% & A partial function\\
{\em x} & R & An element of R\\
}
\Retval{Returns $\sigma x$, or \failed if x is not in the domain of $\sigma$.}
\seealso{\asexp{apply}, \asexp{inDomain?}, \asexp{predicate}}
#endif
} == add {
	Rep == Record(pred: R->Boolean, func: R->S, pfunc: R->Partial S);
	import from Rep;

	mapping(f:%):(R -> S)			== rep(f).func;
	partialMapping(f:%):(R -> Partial S)	== rep(f).pfunc;
	predicate(f:%):(R -> Boolean)		== rep(f).pred;
	apply(f:%, r:R):S			== mapping(f)(r);
	partialApply(f:%, r:R):Partial S	== partialMapping(f)(r);
	inDomain?(f:%, r:R):Boolean		== predicate(f)(r);

	(u:%) = (v:%):Boolean == {
		import from Pointer;
		(u pretend Pointer) =$Pointer (v pretend Pointer);
	}

	partialFunction(f:R -> Partial S):% == {
		import from Partial S;
		per [(r:R):Boolean +-> ~failed? f r, (r:R):S +-> retract f r,f];
	}

	partialFunction(p:R -> Boolean, g:R -> S):% == {
		per [p, g, (r:R):Partial S +-> [g r]];
	}
}
