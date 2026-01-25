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
---------------------------- sal_array.as ----------------------------------
--
-- This file defines arrays with base-translations.
-- Those arrays are 0-indexed and do not carry out bound-checking.
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro {
	A  == PrimitiveArray;
	Z  == MachineInteger;
}

#if ALDOC
\thistype{Array}
\History{Manuel Bronstein}{7/10/98}{created}
\History{Manuel Bronstein}{21/10/99}{added exceptions}
\Usage{import from \this~T}
\Params{{\em T} & Type & the type of the array entries\\}
\Descr{\this~provides arrays of entries of type $T$,
$0$-indexed and without bound checking.}
\begin{exports}
\category{\astype{ArrayType}(T, \astype{PrimitiveArray} T)}\\
\end{exports}
#endif

Array(T:Type): ArrayType(T, A T) == add {
	Rep == Record(size:Z, arr: A T);
	import from A T;

	#(x:%):Z			== { import from Rep; rep(x).size }
	data(x:%):A T			== { import from Rep; rep(x).arr }
	array(p:A T, n:Z):%		== { import from Rep; per [n, p] }
	firstIndex:Z			== 0;
	empty:%				== { import from Z; array(empty, 0) }

	-- TEMPORARY (BUG1182) DEFAULTS DON'T INLINE WELL (NEXT 3 FUNCS)
	apply(a:%, n:Z, m:Z):% == {
		assert(n >= 0 and m >= n and m < #a);
		array(data(a) + n, next(m - n));
	}
	apply(x:%, n:Z):T == {
		assert(n >= 0 and n < #x);
		data(x).n;
	}
	set!(x:%, n:Z, y:T):T == {
		assert(n >= 0 and n < #x);
		data(x).n := y;
	}

	resize!(x:%, n:Z):% == {
		assert(n >= 0);
		a := data x;
		if n > #x then a := resize!(a, #x, n);
		reset!(x, n, a);
	}

	local reset!(x:%, n:Z, a:A T):% == {
		import from Rep;
		rep(x).size := n;
		rep(x).arr := a;
		x;
	}

	copy!(b:%, a:%):% == {
		import from Z;
		q:A T := {
			(n := #a) > #b => new n;
			data b;
		}
		p := data a;		-- optimizes code generation
		for i in 0..prev n repeat q.i := p.i;
		reset!(b, n, q);
	}
}

#if ALDOC
\thistype{ArrayException}
\History{Manuel Bronstein}{21/10/99}{created}
\Usage{
throw \this\\
try \dots catch E in \{ E has \astype{ArrayExceptionType} => \dots \}
}
\Descr{\this~is an exception type thrown by array access.}
#endif
ArrayException: ArrayExceptionType == add;

#if ALDOC
\thistype{ArrayExceptionType}
\History{Manuel Bronstein}{21/10/99}{created}
\Usage{\this: Category}
\Descr{\this~is the category of exceptions thrown by array access.}
#endif
define ArrayExceptionType:Category == with;

#if ALDOC
\thistype{ArrayType}
\History{Manuel Bronstein}{12/04/2000}{created}
\Usage{\this(T, P): Category}
\Params{
{\em T} & Type & the type of the array entries\\
{\em P} & \astype{PrimitiveArrayType} T & the type of the underlying data\\
}
\Descr{\this~is the category of arrays whose entries are of type $T$ and
whose underlying data is of type $P$.}
\begin{exports}
\category{\astype{BoundedFiniteLinearStructureType} T}\\
\asexp{apply}:
& (\%, \astype{MachineInteger}, \astype{MachineInteger}) $\to$ \% & subarray\\
\asexp{array}: & (P, \astype{MachineInteger}) $\to$ \% &
construction of an array\\
\asexp{data}: & \% $\to$ P & access to raw data\\
\asexp{new}: & \astype{MachineInteger} $\to$ \% & creation of an array\\
\asexp{resize!}: & (\%, \astype{MachineInteger}) $\to$ \% & resize an array\\
\asexp{sort!}: & (\%, (T, T) $\to$ \astype{Boolean}) $\to$ \% & sort an array\\
\end{exports}
\begin{exports}[if $T$ has \astype{TotallyOrderedType} then]
\asexp{binarySearch}:
& (\%, T) $\to$ (\astype{Boolean}, \astype{MachineInteger}) & binary search\\
\asexp{sort!}: & \% $\to$ \% & sort an array\\
\end{exports}
#endif

define ArrayType(T:Type, PT:PrimitiveArrayType T):
	Category == BoundedFiniteLinearStructureType T with {
	apply: (%, Z, Z) -> %;
#if ALDOC
\aspage{apply}
\Usage{\name(a, n, m)\\ a(n, m)}
\Signature{(\%, \astype{MachineInteger}, \astype{MachineInteger})}{\%}
\Params{
{\em a} & \% & an array\\
{\em n,m} & \astype{MachineInteger} & indices\\
}
\Retval{Returns the subarray containing the entries $a.n$ to $a.m$ inclusive.
No copying is made.}
#endif
	array: (PT, Z) -> %;
#if ALDOC
\aspage{array}
\Usage{\name(p, n)}
\Signature{(P, \astype{MachineInteger})}{\%}
\Params{
{\em p} & P & a primitive array structure\\
{\em n} & \astype{MachineInteger} & a number of elements\\
}
\Retval{Returns an array containing the first n entries of p.
No copying is made.}
#endif
	if T has TotallyOrderedType then {
		binarySearch: (%, T) -> (Boolean, Z);
#if ALDOC
\aspage{binarySearch}
\Usage{\name(a, t)}
\Signature{(\%, T)}{(\astype{Boolean}, \astype{MachineInteger})}
\Params{
{\em a} & \% & an array\\
{\em t} & T & the value to search for\\
}
\Retval{Returns (found?, i) such that $0 \le i < \#a$ and
$t = a.i$ if found?~is \true. Otherwise, found?~is \false~and:
\begin{itemize}
\item ~if $i < 0$ then $t < a.0$;
\item ~if $i \ge \#a - 1$ then $t > a(\#a-1)$;
\item ~if $0 \le i < \#a - 1$, then $a.i < t < a(i+1)$.
\end{itemize}
The array a must be sorted in increasing order. If a is sorted with respect
to a different order, it is still possible to use binary search, but from
\astype{BinarySearch}.
}
#endif
	}
	data: % -> PT;
#if ALDOC
\aspage{data}
\Usage{\name~a}
\Signature{\%}{P}
\Params{ {\em a} & \% & an array\\ }
\Retval{Returns the raw data of the array a. No copying is made. This function
can be used for efficiency before accessing the elements of a inside a loop,
or in order to pass the elements of a to a C function.}
#endif
	new: Z -> %;
#if ALDOC
\aspage{new}
\Usage{\name~n}
\Signature{\astype{MachineInteger}}{\%}
\Params{ {\em n} & \astype{MachineInteger} & a nonnegative size\\ }
\Retval{Returns an array of $n$ uninitialized entries.}
#endif
	resize!: (%, Z) -> %;
#if ALDOC
\aspage{resize!}
\Usage{\name(a, n)}
\Signature{(\%,\astype{MachineInteger})}{\%}
\Params{
{\em a} & \% & an array\\
{\em n} & \astype{MachineInteger} & a nonnegative size\\
}
\Retval{Returns an array of $n$ entries, whose first $\#a$ entries
are the first $\#a$ entries of $a$ and whose remaining entries are
uninitialized.}
#endif
	sort!: (%, (T, T) -> Boolean) -> %;
	if T has TotallyOrderedType then {
		sort!: % -> %;
	}
#if ALDOC
\aspage{sort!}
\Usage{\name~a\\ \name(a, f)}
\Signature{(\%,(T,T) $\to$ \astype{Boolean})}{\%}
\Params{
{\em a} & \% & a primitive array\\
{\em f} & (T, T) $\to$ \astype{Boolean} & a comparison function\\
}
\Descr{Sorts the array $a$ using the ordering
$x < y \iff f(x,y)$. The comparison function $f$ is optional if
$T$ has \astype{TotallyOrderedType}, in which case the order
function of $T$ is taken.}
#endif
	default {
		import from PT;

		empty?(a:%):Boolean		== { import from Z; zero? #a; }
		free!(x:%):()			== free! data x;
		new(n:Z):%			== array(new n, n);
		new(n:Z, x:T):%			== array(new(n, x), n);
		bracket(t:Tuple T):%		== array(bracket t, length t);
		(x:%) + (n:Z):%			== array(data(x) + n, #x - n);

		sort!(a:%, f:(T, T) -> Boolean):% == {
			import from Z;
			zero?(n := #a) => empty;
			sort!(data a, 0, prev n, f);
			a;
		}

		map!(f:T -> T)(a:%):% == {
			import from Z;
			zero?(n := #a) => empty;
			p := data a;		-- optimizes code generation
			for i in 0..prev n repeat p.i := f(p.i);
			a;
		}

		map(f:T -> T)(a:%):% == {
			import from Z;
			zero?(n := #a) => empty;
			b:% := new n;
			p := data a;		-- optimizes code generation
			q := data b;		-- optimizes code generation
			for i in 0..prev n repeat q.i := f(p.i);
			b;
		}

		copy(a:%):% == {
			import from Z;
			zero?(n := #a) => empty;
			b:% := new n;
			p := data a;		-- optimizes code generation
			q := data b;		-- optimizes code generation
			for i in 0..prev n repeat q.i := p.i;
			b;
		}

		generator(a:%):Generator T == generate {
			import from Z;
			p := data a;		-- optimizes code generation
			for i in 0..prev(#a) repeat yield(p.i);
		}

		bracket(g:Generator T):% == {
			import from Z, List T;
			l:List T := [g];
			a:% := new(n := #l);
			p := data a;		-- optimizes code generation
			for t in l for i in 0.. repeat p.i := t;
			a;
		}

		if T has PrimitiveType then {
			find(t:T, a:%):(%, Z) == {
				p := data a;	-- optimizes code generation
				for n in 0..prev(#a) repeat {
					p.n = t => return(a + n, n);
				}
				(empty, -1);
			}

			(a:%) = (b:%):Boolean == {
				import from Z, T;
				(n := #a) ~= #b => false;
				p := data a;	-- optimizes code generation
				q := data b;	-- optimizes code generation
				for i in 0..prev n repeat {
					p.i ~= q.i => return false;
				}
				true;
			}
		}

		apply(a:%, n:Z, m:Z):% == {
			assert(n >= 0 and m >= n and m < #a);
			array(data(a) + n, next(m - n));
		}

		apply(x:%, n:Z):T == {
			assert(n >= 0 and n < #x);
			data(x).n;
		}

		set!(x:%, n:Z, y:T):T == {
			assert(n >= 0 and n < #x);
			data(x).n := y;
		}

		if T has OutputType then {
			(p:TextWriter) << (a:%):TextWriter == {
				import from String, Boolean, Z, T;
				n := #a;
				x := data a;	-- optimizes code generation
				p := p << "[";
				if ~zero?(n) then p := p << x.0;
				for i in 1..prev n repeat p := p << "," << x.i;
				p << "]";
			}
		}

		if T has InputType then {
			<< (p:TextReader):% == {
				import from Z, List T;
				l:List T := << p;
				empty? l => empty;
				a:% := new(#l, first l);
				for x in l for n in 0.. repeat a.n := x;
				free! l;
				a;
			}
		}

		if T has SerializableType then {
			<< (p:BinaryReader):% == {
				import from Z, T;
				n:Z := << p;		-- read size first
				zero? n => empty;
				array(read(p, n), n);
			}
		}

		if T has TotallyOrderedType then {
			sort!(a:%):% == sort!(a, <$T);

			binarySearch(a:%, t:T):(Boolean, Z) == {
				import from BinarySearch(Z, _
						T pretend TotallyOrderedType);
				p := data a;	-- optimizes code generation
				binarySearch(t, (i:Z):T +-> p.i, 0, prev(#a));
			}
		}
	}
}
