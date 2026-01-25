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
---------------------------- sal_list.as ------------------------------------
--
-- This file defines basic lists
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro {
	Ch == Character;
	Z  == MachineInteger;
}

#if ALDOC
\thistype{List}
\History{Manuel Bronstein}{28/9/98}{created}
\Usage{import from \this~T}
\Params{{\em T} & Type & the type of the list entries\\}
\Descr{\this~provides lists of entries of type $T$, $1$-indexed and without
bound checking.}
\begin{exports}
\category{\astype{BoundedFiniteLinearStructureType} T}\\
\asexp{append!}: & (\%, T) $\to$ \% & adds an entry at the end\\
\asexp{append!}: & (\%, \%) $\to$ \% & adds a list at the end\\
\asexp{cons}: & (T, \%) $\to$ \% & adds an entry at the front\\
\asexp{delete!}: & (\%, \astype{MachineInteger}) $\to$ \% & remove an entry\\
\asexp{first}: & \% $\to$ T & first entry\\
\asexp{rest}: & \% $\to$ \% & all entries after the first\\
\asexp{reverse}: & \% $\to$ \% & reverse a list\\
\asexp{reverse!}: & \% $\to$ \% & reverse a list in--place\\
\asexp{setRest!}: & (\%, \%) $\to$ \% & changes the rest of a list\\
\asexp{sort!}: & (\%, (T, T) $\to$ \astype{Boolean}) $\to$ \% & sort a list\\
\end{exports}
\begin{exports}[if $T$ has \astype{TotallyOrderedType} then]
\asexp{sort!}: & \% $\to$ \% & sort a list\\
\end{exports}
#endif

List(T:Type): BoundedFiniteLinearStructureType T with {
	append!: (%, T) -> %;
	append!: (%, %) -> %;
#if ALDOC
\aspage{append!}
\Usage{\name(l, x)\\ \name(l, s)}
\Signatures{
\name: & (\%, T) $\to$ \%\\
\name: & (\%, \%) $\to$ \%\\
}
\Params{
{\em l,s} & \% & lists\\
{\em x} & T & an entry\\
}
\Retval{\name(l,x) and \name(l,s) return the lists
$[l,x]$ and $[l,s]$ respectively.}
\Remarks{\name~does not make a copy of $l$, which is therefore
modified after the call. It is unsafe to use the variable $l$
after the call, unless it has been assigned to the result
of the call, as in {\tt l := append!(l, x)}.}
\seealso{\asexp{cons}}
#endif
	cons: (T, %) -> %;
#if ALDOC
\aspage{cons}
\Usage{\name(x, l)}
\Signature{(T, \%)}{\%}
\Params{
{\em x} & T & an entry\\
{\em l} & \% & a list\\
}
\Retval{Returns the list $[x, l]$. Does not make a copy of $l$.}
\seealso{\asexp{append!}}
#endif
	delete!: (%, Z) -> %;
#if ALDOC
\aspage{delete!}
\Usage{\name(l, n)}
\Signature{(\%, \astype{MachineInteger})}{\%}
\Params{
{\em l} & \% & a list\\
{\em n} & \astype{MachineInteger} & an index\\
}
\Retval{Returns the list $l$ with $l.n$ removed. Does not make a copy of $l$.}
#endif
	first: % -> T;
#if ALDOC
\aspage{first}
\Usage{\name~l}
\Signature{\%}{T}
\Params{ {\em l} & \% & a nonempty list\\ }
\Retval{Returns the first entry of $l$.}
#endif
	rest: % -> %;
#if ALDOC
\aspage{rest}
\Usage{\name~l}
\Signature{\%}{\%}
\Params{ {\em l} & \% & a nonempty list\\ }
\Retval{Returns $l$ with the first element removed.
Does not make a copy of $l$.}
\seealso{\asexp{setRest!}}
#endif
	reverse: % -> %;
	reverse!: % -> %;
#if ALDOC
\aspage{reverse}
\astarget{\name!}
\Usage{\name~l\\ \name!~l}
\Signature{\%}{\%}
\Params{ {\em l} & \% & a list\\ }
\Retval{\name(l) returns a copy of $l$ with the elements in reverse order,
while \name!(l) reverses $l$ without copying it.}
\Remarks{\name!~does not make a copy of $l$, which is therefore
modified after the call. It is unsafe to use the variable $l$
after the call, unless it has been assigned to the result
of the call, as in {\tt l := reverse!~l}.}
#endif
	setRest!: (%, %) -> %;
#if ALDOC
\aspage{setRest!}
\Usage{\name(l,t)}
\Signature{(\%,\%)}{\%}
\Params{
{\em l} & \% & a nonempty list\\
{\em t} & \% & a list\\
}
\Descr{Replaces l by the list {\tt [first(l),t]} and returns t.}
\Remarks{\name(l,t) does not make a copy of $l$, which is therefore
modified after the call.}
#endif
	sort!: (%, (T, T) -> Boolean) -> %;
	if T has TotallyOrderedType then {
		sort!: % -> %;
	}
#if ALDOC
\aspage{sort!}
\Usage{\name~l\\ \name(l, f)}
\Signature{(\%,(T,T) $\to$ \astype{Boolean})}{\%}
\Params{
{\em l} & \% & a list\\
{\em f} & (T, T) $\to$ \astype{Boolean} & a comparison function\\
}
\Descr{Sorts the list $a$ using the ordering
$x < y \iff f(x,y)$. The comparison function $f$ is optional if
$T$ has \astype{TotallyOrderedType}, in which case the order
function of $T$ is taken.}
\Remarks{\name~does not make a copy of $l$, which is therefore
modified after the call. It is unsafe to use the variable $l$
after the call, unless it has been assigned to the result
of the call, as in {\tt l := \name~l}.}
#endif
} == add {
	Rep == Record(elt:T, next:%);
	import from Rep;

	empty:%				== (nil$Pointer) pretend %;
	empty?(l:%):Boolean		== nil?(l pretend Pointer)$Pointer;
	apply(l:%, n:Z):T		== first(l + prev n);	-- 1-indexed
	cons(x:T, l:%):%			== per [x, l];
	firstIndex:Z				== 1;
	copy(l:%):%				== [x for x in l];
	map(f:T -> T)(l:%):%			== [f x for x in l];
	local comma:Ch				== char 44;
	local leftBracket:Ch			== char 91;
	local rightBracket:Ch			== char 93;
	append!(l:%, x:T):%			== append!(l, cons(x, empty));
	local setEntry!(l:%, e:T):T		== rep(l).elt := e;
	sort!(l:%, less:(T, T) -> Boolean):%	== sort!(l, #l, less);

	setRest!(l:%, s:%):% == {
		import from Boolean;
		assert(~empty? l);
		rep(l).next := s;
	}

	delete!(l:%, n:Z):% == {
		assert(1 <= n); assert(n <= #l);
		n = 1 => rest l;
		ll := l + prev prev n;
		setRest!(ll, rest rest ll);
		l;
	}

	copy!(m:%, l:%):% == {
		import from Boolean;
		ans := m;
		last:% := empty;
		while ~(empty? m or empty? l) repeat {
			setEntry!(m, first l);
			last := m;
			m := rest m;
			l := rest l;
		}
		if ~empty?(last) then setRest!(last, copy l);
		ans;
	}

	reverse!(l:%):% == {
		import from Boolean;
		empty? l => l;
		forward := rest l;
		setRest!(l, empty);
		while ~empty? forward repeat {
			t := rest forward;
			setRest!(forward, l);
			l := forward;
			forward := t;
		}
		l;
	}

	append!(l:%, s:%):% == {
		import from Boolean;
		ans := chase := l;
		while ~empty? l repeat {
			chase := l;
			l := rest l;
		}
		empty? chase => s;		-- l was empty at the start
		assert(empty? rest chase);
		setRest!(chase, s);
		ans;
	}

	map!(f:T -> T)(l:%):% == {
		import from Boolean;
		ll := l;
		while ~empty? l repeat {
			rep(l).elt := f first l;
			l := rest l;
		}
		ll;
	}

	new(n:Z, t:T):% == {
		l := empty;
		for i in 1..n repeat l := cons(t, l);
		l;
	}

	set!(l:%, n:Z, x:T):T == {
		assert(1 <= n);
		r := rep(l + prev n);	-- 1-indexed so translate by n-1
		r.elt := x;
	}

	generator(l:%):Generator T == generate {
		import from Boolean;
		while ~empty? l repeat {
			yield first l;
			l := rest l;
		}
	}

	free!(l:%):() == {
		import from Boolean, Machine;
		while ~empty? l repeat {
			rec := rep l;
			l := rest l;
			dispose! rec;
		}
	}

	bracket(t:Tuple T):% == {
		import from Z;
		l := empty;
		for n in length(t)..1 by -1 repeat l := cons(element(t, n), l);
		l;
	}

	bracket(g:Generator T):% == {
		h := l := empty;
		for t in g repeat {
			temp := l;
			l := cons(t, empty);
			if empty? temp then h := l; else rep(temp).next := l;
		}
		h;
	}

	local sort!(l:%, n:Z, less:(T, T) -> Boolean):%	== {
		assert(n = #l);
		n < 2 => l;
		n = 2 => {
			less(first l, first rest l) => l;
			reverse! l;
		}
		-- break l in the middle (in-place)
		m := n quo 2;
		assert(m >= 1);
		t := l + prev m;	-- will be last elt of first-half
		l2 := rest t;		-- second half
		setRest!(t, empty);	-- break l into 2 pieces (l and l2)
		assert(#l = m); assert(#l2 = n - m);
		l := sort!(l, m, less);
		l2 := sort!(l2, n - m, less);
		merge!(l, l2, less);
	}

	-- l1 and l2 must be sorted in ascending order
	local merge!(l1:%, l2:%, less:(T, T) -> Boolean):% == {
		import from Boolean;
		empty? l1 => l2;
		empty? l2 => l1;
		local l:%;
		if less(first l1, first l2)	then { l := l1; l1 := rest l1 }
						else { l := l2; l2 := rest l2 }
		t := l;
		while (~empty? l1) and (~empty? l2) repeat {
			if less(first l1, first l2) then {
				setRest!(t, l1);
				t := l1;
				l1 := rest l1;
			}
			else {
				setRest!(t, l2);
				t := l2;
				l2 := rest l2;
			}
		}
		setRest!(t, { empty? l1 => l2; l1 });
		l;
	}

	if T has PrimitiveType then {
		find(t:T, l:%):(%, Z) == {
			import from Boolean;
			while ~empty? l for n in firstIndex.. repeat {
				t = first l => return(l, n);
				l := rest l;
			}
			(empty, -1);
		}

		(l1:%) = (l2:%):Boolean == {
			while ~empty?(l1) repeat {
				empty? l2 or (first l1 ~= first l2) =>
								return false;
				l1 := rest l1;
				l2 := rest l2;
			}
			empty? l2;
		}
	}

	first(l:%):T == {
		import from Boolean;
		assert(~empty? l);
		rep(l).elt;
	}

	rest(l:%):% == {
		import from Boolean;
		assert(~empty? l);
		rep(l).next;
	}

	(l:%) + (n:Z):% == {
		assert(0 <= n); assert(n <= #l);
		for i in 1..n repeat l := rest l;
		l;
	}

	#(l:%):Z == {
		import from Boolean;
		n:Z := 0;
		while ~empty?(l) repeat { l := rest l; n := next n; }
		n::Z;
	}

	reverse(l:%):% == {
		rl := empty;
		for x in l repeat rl := cons(x, rl);
		rl;
	}

	if T has OutputType then {
		(p:TextWriter) << (l:%):TextWriter == {
			import from Character, Boolean, T;
			p := p << leftBracket;
			if ~empty?(l) then {
				p := p << first l;
				while ~empty?(l := rest l) repeat
					p := p << comma << first l;
			}
			p << rightBracket;
		}
	}

	if T has SerializableType then {
		<< (p:BinaryReader):% == {
			import from Z, T;
			l:% := empty;
			n:Z := << p;			-- read size first
			for i in 1..n repeat l := cons(<< p, l);
			reverse! l;
		}
	}

	if T has InputType then {
		<< (p:TextReader):% == {
			import from Character, Z, T;
			local c:Character;
			while space?(c := << p) repeat {};
			l := empty;
			c ~= leftBracket => l;
			c := comma;
			while c = comma repeat {
				l := cons(<< p, l);
				while space?(c := << p) repeat {};
			}
			c = rightBracket => reverse! l;
			push!(c, p);
			empty;			-- syntax error
		}
	}

	if T has TotallyOrderedType then {
		sort!(a:%):% == sort!(a, <$T);
	}
}

