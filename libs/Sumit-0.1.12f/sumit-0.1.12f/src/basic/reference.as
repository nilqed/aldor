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
------------------------------- reference.as ----------------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1994-95

#include "sumit.as"

#if ASDOC
\thistype{Reference}
\History{Manuel Bronstein}{9/6/94}{created}
\Usage{import from \this~T}
\Params{ {\em T} & Type & The type of objects being pointed to }
\Descr{\this~provides references to elements of T.}
\begin{exports}
\category{BasicType}\\
apply:   & \% $\to$ T & get the value pointed to\\
nil: & \% & the nil pointer\\
nil?: & \% $\to$ Boolean &
test whether a reference is the nil pointer\\
ref: & T $\to$ \% & get a reference to an element\\
set!:    & (\%, T) $\to$ T & set the value pointed to\\
\end{exports}
#endif

Reference(T:Type): BasicType with {
	apply: % -> T;
#if ASDOC
\begin{aspage}{apply}
\Usage{\name~p\\ p()}
\Signature{\this~T}{T}
\Params{ {\em p} & \this~T & The pointer to dereference\\ }
\Retval{Returns the element that p points to.}
\seealso{ref(\this)}
\end{aspage}
#endif
	nil: %;
#if ASDOC
\begin{aspage}{nil}
\Usage{\name}
\Signature{}{\this~T}
\Retval{Returns the nil pointer.}
\seealso{nil?(\this)}
\end{aspage}
#endif
	nil?: % -> Boolean;
#if ASDOC
\begin{aspage}{nil?}
\Usage{\name p}
\Signature{\this~T}{Boolean}
\Params{ {\em p} & \this~T & The pointer to test\\ }
\Retval{Returns \true~if p is the nil pointer, \false~otherwise.}
\seealso{nil(\this)}
\end{aspage}
#endif
	ref: T -> %;
#if ASDOC
\begin{aspage}{ref}
\Usage{\name~x}
\Signature{T}{\this~T}
\Params{ {\em x} & T & The element to be referred to\\ }
\Retval{Returns a reference pointing to x.}
\seealso{apply(\this)}
\end{aspage}
#endif
	set!: (%, T) -> T
#if ASDOC
\begin{aspage}{set!}
\Usage{ \name(p, x)\\p() := x }
\Signature{(\this~T, T)}{T}
\Params{
{\em p} & \this~T & The pointer to set\\
{\em x} & T & The element p should point to\\
}
\Descr{Modifies the value pointed to by p by setting it to x.}
\Retval{Returns the new value x.}
\seealso{apply(\this), ref(\this)}
\end{aspage}
#endif
-- TEMPORARY: COMPILE TIME BUG IN 1.0.6
-- } == NilRecord(val:T) add {
-- 	macro Rep == NilRecord(val:T);
} == NilRecord T add {
	macro Rep == NilRecord T;

	import from Rep;

	sample:%			== nil;
	(p:%) = (q:%):Boolean		== eq?(rep p, rep q);
	ref(x:T):%			== per [x];

	apply(p:%):T == {
		-- TEMPORARY: COMPILE TIME BUG IN 1.0.6
		-- import from Record(val:T);
		-- record(rep p).val
		import from Record T;
		explode record rep p;
	}

	set!(p:%, x:T):T == {
		import from Record(val:T);
		-- TEMPORARY: COMPILE TIME BUG IN 1.0.6
		-- record(rep p).val := x
		r := record rep p;
		s := r pretend Record(val:T);
		s.val := x;
	}

	(p:TextWriter) << (q:%):TextWriter == {
		nil? q => p << "NIL";
		p << "ref(*)";
	}
}

#if SUMITTEST
---------------------- test reference.as --------------------------
#include "sumittest.as"

reference():Boolean == {
	import from SingleInteger, Reference SingleInteger;

	n := 5;
	m := 2;
	r := ref n;
	p := r();
	r() := n + m;
	p = n and r() - n = m and ~nil? r;
}

print << "Testing reference..." << newline;
sumitTest("reference", reference);
print << newline;
#endif

