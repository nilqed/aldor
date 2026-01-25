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
---------------------------- sal_parray.as ----------------------------------
--
-- This file defines primitive arrays with base-translations.
-- Those arrays are 0-indexed and do not do bound-checking.
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro Z == MachineInteger;

#if ALDOC
\thistype{PrimitiveArray}
\History{Manuel Bronstein}{28/9/98}{created}
\Usage{import from \this~T}
\Params{{\em T} & Type & the type of the array entries\\}
\Descr{\this~provides arrays of entries of type $T$,
$0$-indexed and without bound checking (the debug version
of \salli provides bound--checking for primitive arrays).}
\begin{exports}
\category{\astype{PrimitiveArrayType} T}\\
\end{exports}
#endif

PrimitiveArray(T:Type): PrimitiveArrayType T == add {
	import from Machine;
#if DEBUG
	Rep == Record(sz:Z, data:Arr);
	local data(x:%):Arr	== { import from Rep; rep(x).data }
	local size(x:%):Z	== { import from Rep; rep(x).sz; }
	local arr(x:Arr, n:Z):%	== { import from Rep; per [n, x]; }
#else
	Rep == Arr;
	local data(x:%):Arr	== rep x;
	local arr(x:Arr, n:Z):%	== per x;
	local arr(x:Arr):%	== per x;
#endif

	pointer(a:%):Pointer		== int(a)::Pointer;
	empty:%				== (nil$Pointer) pretend %;
	empty?(a:%):Boolean		== nil?(a pretend Pointer)$Pointer;
	local zsize:Z			== bytes$Z;
	firstIndex:Z			== 0;

	free!(x:%):() == {
		import from Boolean;
		if ~empty?(x) then dispose! data x;
	}

	resize!(a:%, oldsz:Z, newsz:Z):% == {
		assert(oldsz >= 0); assert(newsz >= 0);
		newsz <= oldsz => a;
		b := new newsz;
		for i in 0..prev oldsz repeat b.i := a.i;
		free! a;
		b;
	}

	new(n:Z):% == {
		assert(n >= 0);
		AGAT("parraynew", n);
		arr(array(Z)(0, n::SInt), n);
	}

	new(n:Z, x:T):%	== {
		assert(n >= 0);
		AGAT("parraynew", n);
		a := array(T)(x, n::SInt);
		for i in 0..prev n repeat set!(T)(a, i::SInt, x);
		arr(a, n);
	}

#if DEBUG
	array(p:Pointer, n:Z):%	== arr(p pretend Arr, n);

	apply(x:%, n:Z):T == {
		assert(n >= 0); assert(n < size x);
		get(T)(data x, n::SInt);
	}

	set!(x:%, n:Z, y:T):T == {
		assert(n >= 0); assert(n < size x);
		set!(T)(data x, n::SInt, y);
	}

	(x:%) + (n:Z):% == {
		assert(0 <= n);
		p:Ptr := convert((int(x) + n * zsize)::SInt);
		arr(p pretend Arr, size(x) - n);
	}
#else
	array(p:Pointer, n:Z):%		== p pretend %;
	apply(x:%, n:Z):T		== get(T)(data x, n::SInt);
	set!(x:%, n:Z, y:T):T		== set!(T)(data x, n::SInt, y);

	(x:%) + (n:Z):% == {
		assert(0 <= n);
		p:Ptr := convert((int(x) + n * zsize)::SInt);
		arr(p pretend Arr);
	}
#endif

	bracket(g:Generator T):% == {
		import from Z, List T;
		l:List T := [g];
		a:% := new(n := #l);
		for t in l for i in 0.. repeat a.i := t;
		a;
	}

	local int(a:%):Z == {
		r := data a;
		-- COMPILER BUG: convert(r)@SInt returns 0!
		-- n:SInt := convert r;
		n:SInt := r pretend SInt;
		n::Z;
	}

	bracket(t:Tuple T):% == {
		import from Z;
		zero?(n := length t) => empty;
		a := new n;
		for i in 0..prev n repeat a.i := element(t, next i);
		a;
	}

	if T has PrimitiveType then {
		equal?(a:%, b:%, n:Z):Boolean == {
			import from T;
			assert(0 <= n);
			-- must go by increasing indices to avoid
			-- ArrayException for unequal arrays
			for i in 0..prev n repeat a.i ~= b.i => return false;
			true;
		}
	}
}

#if ALDOC
\thistype{PrimitiveArrayType}
\History{Manuel Bronstein}{25/5/2000}{created}
\Usage{import from \this~T}
\Params{{\em T} & Type & the type of the array entries\\}
\Descr{\this~is the category of primitive arrays whose entries are of type $T$.}
\begin{exports}
\category{\astype{FiniteLinearStructureType} T}\\
\asexp{array}: & (\astype{Pointer}, Z) $\to$ \% &
conversion from a C--array\\
\asexp{new}: & Z $\to$ \% & creation of an array\\
\asexp{pointer}: & \% $\to$ \astype{Pointer} &
conversion to a C--array\\
\asexp{resize!}: & (\%, Z, Z) $\to$ \% & resize an array\\
\asexp{sort!}:
& (\%, Z, Z, (T, T) $\to$ \astype{Boolean}) $\to$ \% & sort an array\\
\end{exports}
\begin{exports}[if $T$ has \astype{SerializableType} then]
\asexp{read}:
& (\astype{BinaryReader}, Z) $\to$ \% & read using binary encoding\\
\asexp{write}:
& (\astype{BinaryWriter}, %, Z) $\to$ \astype{BinaryWriter} &
write using binary encoding\\
\end{exports}
\begin{exports}[if $T$ has \astype{TotallyOrderedType} then]
\asexp{sort!}: & (\%, Z, Z) $\to$ \% & sort an array\\
\end{exports}
\begin{aswhere}
Z &==& \astype{MachineInteger}\\
\end{aswhere}
#endif

define PrimitiveArrayType(T:Type):Category == FiniteLinearStructureType T with {
	array: (Pointer, Z) -> %;
	pointer: % -> Pointer;
#if ALDOC
\aspage{array,pointer}
\astarget{pointer}
\astarget{string}
\Usage{array(p, n)\\ pointer~a}
\Signatures{
array: & (\astype{Pointer}, \astype{MachineInteger}) $\to$ \%\\
pointer: & \% $\to$ \astype{Pointer}\\
}
\Params{
{\em p} & \astype{Pointer} & a C--array\\
{\em n} & \astype{MachineInteger} & a nonnegative size\\
{\em a} & \% & A primitive array\\
}
\Descr{Use those functions to safely convert between pointers
returned or needed by C--functions and primitive arrays.
Those function have no effect
in the release version of \salli, but they are
necessary when using the debug version, so it is recommended to use
them in all cases.}
#endif
	new: Z -> %;
#if ALDOC
\aspage{new}
\Usage{\name~n}
\Signature{\astype{MachineInteger}}{\%}
\Params{ {\em n} & \astype{MachineInteger} & a nonnegative size\\ }
\Retval{Returns a primitive array of $n$ uninitialized entries.}
#endif
	if T has SerializableType then {
		read: (BinaryReader, Z) -> %;
		write: (BinaryWriter, %, Z) -> BinaryWriter;
#if ALDOC
\aspage{read,write}
\astarget{read}
\astarget{write}
\Usage{read(in, n)\\ write(out, a, n)}
\Signatures{
read: & (\astype{BinaryReader}, \astype{MachineInteger}) $\to$ \%\\
write:
& (\astype{BinaryWriter}, \%, \astype{MachineInteger})
$\to$ \astype{BinaryWriter}\\
}
\Params{
{\em in} & \astype{BinaryReader} & an input stream\\
{\em out} & \astype{BinaryWriter} & an output stream\\
{\em n} & \astype{MachineInteger} & a nonnegative size\\
{\em a} & \% & A primitive array\\
}
\Retval{read(in, n) reads a primitive array of $n$ elements
in binary format from the stream in and
returns the array read, while
write(out, a, n) writes the first $n$ elements of $a$ to the stream out
and returns the stream after the write.}
#endif
	}
	resize!: (%, Z, Z) -> %;
#if ALDOC
\aspage{resize!}
\Usage{\name(a, n, m)}
\Signature{(\%,\astype{MachineInteger},\astype{MachineInteger})}{\%}
\Params{
{\em a} & \% & a primitive array\\
{\em n, m} & \astype{MachineInteger} & nonnegative sizes\\
}
\Retval{Returns a primitive array of $m$ entries, whose first $n$ entries
are the first $n$ entries of $a$ and whose remaining entries are
uninitialized.}
\Remarks{\name~may free the space previously used by $a$, so
it is unsafe to use the variable $a$
after the call, unless it has been assigned to the result
of the call, as in {\tt a := resize!(a, n, m)}.}
#endif
	sort!: (%, Z, Z, (T, T) -> Boolean) -> %;
	if T has TotallyOrderedType then {
		sort!: (%, Z, Z) -> %;
	}
#if ALDOC
\aspage{sort!}
\Usage{\name(a, n, m)\\ \name(a, n, m, f)}
\Signature{(\%,\astype{MachineInteger},\astype{MachineInteger},
(T,T) $\to$ \astype{Boolean})}{\%}
\Params{
{\em a} & \% & a primitive array\\
{\em n, m} & \astype{MachineInteger} & indices\\
{\em f} & (T, T) $\to$ \astype{Boolean} & a comparison function\\
}
\Descr{Sorts the subarray $[a.n,\dots,a.m]$ using the ordering
$x < y \iff f(x,y)$. The comparison function $f$ is optional if
$T$ has \astype{TotallyOrderedType}, in which case the order
function of $T$ is taken.}
#endif
	default {
		if T has SerializableType then {
			read(p:BinaryReader, n:Z):% == {
				import from T;
				assert(n >= 0);
				zero? n => empty;
				a := new n;
				for m in 1..n repeat a.m := << p;
				a;
			}

			write(p:BinaryWriter, a:%, n:Z):BinaryWriter == {
				import from T;
				assert(n >= 0);
				for m in 1..n repeat p := p << a.m;
				p;
			}
		}

		if T has TotallyOrderedType then {
			sort!(a:%, n:Z, m:Z):% == sort!(a, n, m, <$T);
		}

		sort!(a:%, n:Z, m:Z, less:(T, T) -> Boolean):% == {
			assert(n >= 0); assert(m >= 0);
			(s := m - n) <= 0 => a;
			s = 1 => {
				less(a.n, a.m) => a;
				swap!(a, n, m);
			}
			k := partition(a, n, m, less);
			sort!(a, n, k, less);
			sort!(a, next k, m, less);
		}

		local swap!(a:%, n:Z, m:Z):% == {
			t := a.n;
			a.n := a.m;
			a.m := t;
			a;
		}

		local partition(a:%, n:Z, m:Z, less:(T, T) -> Boolean):Z == {
			import from Boolean;
			assert(m > next n);
			r := n + (random()$Z mod next(m-n));
			swap!(a, r, n);		-- randomize the array
			x := a.n;		-- (random) pivot
			i := next n;
			j := m;
			while i < j repeat {
				while i<= m and ~less(x,a.i) repeat i := next i;
				if i > m then {		-- x = max(a[n..m])
					swap!(a, n, m);
					return prev m;
				}
				while j > n and ~less(a.j,x) repeat j := prev j;
				if i < j then {
					swap!(a, i, j);
					i := next i;
					j := prev j;
				}
			}
			j;
		}
	}
}
