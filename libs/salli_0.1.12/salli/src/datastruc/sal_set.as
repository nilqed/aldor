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
---------------------------- sal_set.as ------------------------------------
--
-- This file defines basic sets
--
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro {
	Ch == Character;
	Z  == MachineInteger;
}

#if ALDOC
\thistype{Set}
\History{Manuel Bronstein}{9/11/99}{created}
\Usage{import from \this~T}
\Params{{\em T} & \astype{PrimitiveType} & the type of the set entries\\}
\Descr{\this~provides sets of entries of type $T$, $1$-indexed and without
bound checking.}
\begin{exports}
\category{\astype{BoundedFiniteLinearStructureType} T}\\
\asexp{$-$}: & (\%, \%) $\to$ \% & set difference\\
\asexp{intersection}: & (\%, \%) $\to$ \% & intersect two sets\\
\asexp{intersection!}: & (\%, \%) $\to$ \% & intersect two sets\\
\asexp{minus!}: & (\%, \%) $\to$ \% & set difference\\
\asexp{union}: & (\%, T) $\to$ \% & add an element\\
               & (\%, \%) $\to$ \% & add a set of elements\\
\asexp{union!}: & (\%, T) $\to$ \% & add an element\\
                & (\%, \%) $\to$ \% & add a set of elements\\
\end{exports}
#endif

Set(T:PrimitiveType): BoundedFiniteLinearStructureType T with {
	-: (%, %) -> %;
#if ALDOC
\aspage{$-$}
\Usage{$x - y$}
\Signature{(\%, \%)}{\%}
\Params{ {\em x,y} & \% & sets\\ }
\Retval{Return $x - y = \{ a \in x \st a \notin y\}$.}
\seealso{\asexp{minus!}}
#endif
	intersection: (%, %) -> %;
	intersection!: (%, %) -> %;
#if ALDOC
\aspage{intersection}
\astarget{\name!}
\Usage{\name(x,y)\\ \name!(x,y)}
\Signature{(\%, \%)}{\%}
\Params{ {\em x,y} & \% & sets\\ }
\Retval{Return $x \cap y = \{ a \st a \in x \mbox{ and } a \in y\}$.}
\Remarks{\name!~does not make a copy of $x$, which is therefore
modified after the call. It is unsafe to use the variable $x$
after the call, unless it has been assigned to the result
of the call, as in {\tt x := \name!(x, y)}.}
#endif
	minus!: (%, %) -> %;
#if ALDOC
\aspage{minus!}
\Usage{\name(x,y)}
\Signature{(\%, \%)}{\%}
\Params{ {\em x,y} & \% & sets\\ }
\Descr{Return $x - y = \{ a \in x \st a \notin y\}$.}
\Remarks{\name~does not make a copy of $x$, which is therefore
modified after the call. It is unsafe to use the variable $x$
after the call, unless it has been assigned to the result
of the call, as in {\tt x := \name(x, y)}.}
\seealso{\asexp{$-$}}
#endif
	union: (%, T) -> %;
	union: (%, %) -> %;
	union!: (%, T) -> %;
	union!: (%, %) -> %;
#if ALDOC
\aspage{union}
\astarget{\name!}
\Usage{\name(x,t)\\ \name(x,y)\\ \name!(x,t)\\ \name!(x,y)}
\Signature{(\%, \%)}{\%}
\Params{
{\em x,y} & \% & sets\\
{\em t} & T & an element\\
}
\Retval{\name(x,y) and \name!(x,y) both
return $x \cup y = \{ a \st a \in x \mbox{ or } a \in y\}$,
while \name(x,t) and \name!(x,t) both return $x \cup \{t\}$.}
\Remarks{\name!~does not make a copy of $x$, which is therefore
modified after the call. It is unsafe to use the variable $x$
after the call, unless it has been assigned to the result
of the call, as in {\tt x := \name!(x, y)}.}
#endif
} == add {
	Rep == List T;
	import from Rep;

	empty:%				== per empty;
	empty?(l:%):Boolean		== empty? rep l;
	apply(l:%, n:Z):T		== rep(l).n;
	firstIndex:Z			== firstIndex$Rep;
	copy(l:%):%			== per copy rep l;
	#(l:%):Z			== #(rep l);
	generator(l:%):Generator T	== generator rep l;
	free!(l:%):()			== free! rep l;
	(l:%) + (n:Z):%			== per(rep(l) + n);
	union(l:%, x:T):%		== union!(copy l, x);
	union(l1:%, l2:%):%		== union!(copy l1, l2);
	intersection(l1:%, l2:%):%	== intersection!(copy l1, l2);
	(l1:%) - (l2:%):%		== minus!(copy l1, l2);
	map(f:T -> T)(l:%):%		== map!(f)(copy l);
	copy!(m:%, l:%):%		== per copy!(rep m, rep l);
	local comma:Ch			== char 44;
	local leftBracket:Ch		== char 123;
	local rightBracket:Ch		== char 125;

	map!(f:T -> T)(l:%):% == {
		empty? l  => empty;
		ll := rep l;
		ll.1 := f first ll;
		lr := map!(f)(per rest ll);
		member?(first ll, lr) => lr;
		per setRest!(ll, rep lr);
	}

	minus!(l1:%, l2:%):% == {
		empty? l1 or empty? l2 => l1;
		x := first(l := rep l1);
		ll := per rest l;
		member?(x, l2) => minus!(ll, l2);
		per setRest!(l, rep minus!(ll, l2));
	}

	intersection!(l1:%, l2:%):% == {
		empty? l1 or empty? l2 => empty;
		x := first(l := rep l1);
		ll := per rest l;
		member?(x, l2) => per setRest!(l, rep intersection!(ll, l2));
		intersection!(ll, l2);
	}

	union!(l:%, x:T):% == {
		member?(x, l) => l;
		per cons(x, rep l);
	}

	union!(l1:%, l2:%):% == {
		for x in l2 repeat l1 := union!(l1, x);
		l1;
	}

	new(n:Z, t:T):% == {
		assert(n >= 0);
		zero? n => empty;
		[t];
	}

	set!(l:%, n:Z, x:T):T == {
		assert(1 <= n);
		(ll, m) := find(x, rep l);
		rep(l).n := x;
		empty? ll or n = m => x;	-- no other occurence of x in l
		delete!(rep l, max(n, m));
		x;
	}

	bracket(t:Tuple T):% == {
		import from Z;
		l:% := empty;
		for n in length(t)..1 by -1 repeat l := union!(l, element(t,n));
		l;
	}

	bracket(g:Generator T):% == {
		l:% := empty;
		for t in g repeat l := union!(l, t);
		l;
	}

	find(t:T, l:%):(%, Z) == {
		(ll, n) := find(t, rep l);
		(per ll, n);
	}

	(l1:%) = (l2:%):Boolean == {
		import from Z;
		#l1 ~= #l2 => false;
		for a in l1 repeat ~member?(a, rep l2) => return false;
		true;
	}

	if T has OutputType then {
		(p:TextWriter) << (l:%):TextWriter == {
			import from Character, Boolean, T;
			p := p << leftBracket;
			if ~empty?(ll := rep l) then {
				p := p << first ll;
				while ~empty?(ll := rest ll) repeat
					p := p << comma << first ll;
			}
			p << rightBracket;
		}
	}

	if T has SerializableType then {
		<< (p:BinaryReader):% == {
			import from Z, T;
			l:% := empty;
			n:Z := << p;			-- read size first
			for i in 1..n repeat l := union!(l, (<< p)@T);
			l;
		}
	}

	if T has InputType then {
		<< (p:TextReader):% == {
			import from Character, Z, T;
			local c:Character;
			while space?(c := << p) repeat {};
			l:% := empty;
			c ~= leftBracket => l;
			c := comma;
			while c = comma repeat {
				l := union!(l, (<< p)@T);
				while space?(c := << p) repeat {};
			}
			c = rightBracket => l;
			push!(c, p);
			empty;			-- syntax error
		}
	}
}
