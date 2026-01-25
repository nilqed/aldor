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
---------------------------- sal_hash.as ------------------------------------
--
-- This file defines hash tables
--
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 29-10-98
-- Logiciel Salli ©INRIA 1999, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro {
	A == Array;
	L == List;
	Z == MachineInteger;
	Ch==Character;
}

#if ALDOC
\thistype{HashTable}
\History{Manuel Bronstein}{14/6/99}{created}
\Usage{import from \this(K, V, h)}
\Params{
{\em K} & \astype{PrimitiveType} & the type of the keys\\
	& \astype{HashType} & \\
{\em V} & Type & the type of the entries\\
{\em h} & K $\to$ \astype{MachineInteger} & the hash function to use\\
}
\Descr{\this~provides hash tables with keys of type $K$,
entries of type $V$ and that uses the hash--function $h$.
If $K$ has \astype{HashType}, then the parameter $h$ is
optional as the function \asfunc{HashType}{hash} is used
by default in that case.}
\begin{exports}
\asexp{apply}: & (\%, K) $\to$ V & extraction of an entry\\
       & (\%, \astype{MachineInteger}, \astype{MachineInteger}) $\to$ V & \\
\asexp{find}: & (\%, K) $\to$ \astype{Partial} V & search for an entry\\
\asexp{free!}: & \% $\to$ () & memory disposal\\
\asexp{insert!}:
& (\%, K, V) $\to$ (\astype{MachineInteger}, \astype{MachineInteger})
& modification of an entry\\
\asexp{set!}: & (\%, K, V) $\to$ V & modification of an entry\\
\asexp{table}: & \astype{MachineInteger} $\to$ \% & creation of a table\\
\end{exports}
\begin{exports}[if $K$ has InputType and $V$ has InputType then]
\category{\astype{InputType}}\\
\end{exports}
\begin{exports}[if $K$ has OutputType and $V$ has OutputType then]
\category{\astype{OutputType}}\\
\end{exports}
\begin{exports}[if $K$ has SerializableType and $V$ has SerializableType then]
\category{\astype{SerializableType}}\\
\end{exports}
#endif

-- This category is defined only as a macro because HashTable is overloaded
define HashCategory(K:PrimitiveType, V:Type): Category == with {
	if K has InputType and V has InputType then InputType;
	if K has OutputType and V has OutputType then OutputType;
	if K has SerializableType and V has SerializableType then
							SerializableType;
	apply: (%, K) -> V;
	apply: (%, Z, Z) -> V;
#if ALDOC
\aspage{apply}
\Usage{\name(t, k)\\ \name(t, i, j)\\ t.k \\ t(i,j)}
\Signatures{
\name: & (\%, K) $\to$ V\\
\name: & (\%, \astype{MachineInteger}, \astype{MachineInteger}) $\to$ V\\
}
\Params{
{\em t} & \% & a table\\
{\em k} & K & a key\\
{\em i,j} & \astype{MachineInteger} & indices returned by
\asexp{insert!}\\
}
\Retval{\name(t,k) and $t.k$ return the element of $t$ with key $k$,
which must be present in the table, while \name(t,i,j) and $t(i,j)$
can be used as shortcuts, only with the pair $(i,j)$ that was returned
by \asexp{insert!} when $k$ was inserted.}
\seealso{\asexp{find}, \asexp{insert!}}
#endif
	find: (%, K) -> Partial V;
#if ALDOC
\aspage{find}
\Usage{\name(t, k)}
\Signature{(\%, K)}{\astype{Partial} V}
\Params{
{\em t} & \% & a table\\
{\em k} & K & a key\\
}
\Retval{Returns \failed if there is no element with key $k$ in $t$,
the element of $t$ with key $k$ otherwise.}
\seealso{\asexp{apply}}
#endif
	free!: % -> ();
#if ALDOC
\aspage{free!}
\Usage{\name~t}
\Signature{\%}{()}
\Params{{\em t} & \% & a table\\}
\Descr{Releases the memory occupied by $t$.}
#endif
	insert!: (%, K, V) -> (Z, Z);
#if ALDOC
\aspage{insert!}
\Usage{\name(t, k, v)}
\Signature{(\%, K, V)}{(\astype{MachineInteger}, \astype{MachineInteger})}
\Params{
{\em t} & \% & a table\\
{\em k} & K & a key\\
{\em v} & V & an entry\\
}
\Retval{Sets the element of $t$ with key $k$ to $v$ and returns
a pair of integers $(i,j)$ identifying $k$ uniquely.}
\Remarks{The pair $(i,j)$ is guaranteed to remain assigned to $k$
during the lifetime of the table, so it can be used to sort the
entries in the table, using any ordering on $\bb{N}^2$. It can also
be used to access $k$ in the table if needed.}
\seealso{\asexp{apply}, \asexp{set!}}
#endif
	set!: (%, K, V) -> V;
#if ALDOC
\aspage{set!}
\Usage{\name(t, k, v)\\ t.k := v; }
\Signature{(\%, K, V)}{V}
\Params{
{\em t} & \% & a table\\
{\em k} & K & a key\\
{\em v} & V & an entry\\
}
\Retval{Sets the element of $t$ with key $k$ to $v$ and returns $v$.}
\seealso{\asexp{insert!}}
#endif
	table: Z -> %;
#if ALDOC
\aspage{table}
\Usage{\name~n}
\Signature{\astype{MachineInteger}}{\%}
\Params{ {\em n} & \astype{MachineInteger} & a positive size\\ }
\Retval{Returns a table of $n$ buckets.}
#endif
}

-- TEMPORARY: WORKAROUND FOR BUG1167
-- HashTable(K:HashType, V:Type):HashCategory(K, V) == HashTable(K, V, hash$K);
HashTable(K:HashType, V:Type):HashCategory(K, V) == HashTable(K, V, hash$K) add;

HashTable(K:PrimitiveType, V:Type, hash: K -> Z): HashCategory(K, V) == add {
	local Entry: with {
		entry: (K, V) -> %;
		free!: % -> ();
		key: % -> K;
		setValue!: (%, V) -> ();
		value: % -> V;
	} == add {
		macro Rep == Record(cle: K, ntry: V);

		key(e:%):K		== { import from Rep; rep(e).cle }
		value(e:%):V		== { import from Rep; rep(e).ntry }
		entry(k:K, v:V):%	== { import from Rep; per [k, v] }
		setValue!(e:%, v:V):()	== { import from Rep; rep(e).ntry := v }
		free!(e:%):()		== { import from Rep; dispose! rep e }
	}

	macro Rep == A L Entry;

	set!(t:%, k:K, v:V):V		== { insert!(t, k, v); v }
	local htable(t:%):A L Entry	== rep t;
	local size(t:%):Z		== { import from A L Entry;#(htable t) }
	local index(t:%, k:K):Z		== hash(k) mod size(t);
	local leftBracket:Ch		== { import from String; char "[" }
	local rightBracket:Ch		== { import from String; char "]" }
	local comma:Ch			== { import from String; char "," }

	apply(t:%, i:Z, j:Z):V == {
		import from Entry, L Entry, A L Entry;
		value(htable(t).i.j);
	}

	table(n:Z):% == {
		import from A L Entry, L Entry;
		assert(n > 0);
		per new(n, empty);
	}

	free!(t:%):() == {
		import from Boolean, Entry, L Entry, A L Entry;
		for l in htable t repeat {
			for e in l repeat free! e;
			if ~empty? l then free! l;
		}
		free! htable t;
	}

	insert!(t:%, k:K, v:V):(Z, Z) == {
		import from Boolean, Entry, L Entry, A L Entry;
		(found?, l, i, j) := search(t, k);
		found? => {
			assert(~empty? l);
			setValue!(first l, v);
			(i, j);
		}
		e := entry(k, v);
		if empty? l then htable(t).i := cons(e,empty);else append!(l,e);
		(i, next j);
	}

	-- to be used only when k may or may not appear in t
	find(t:%, k:K):Partial V == {
		import from Boolean, Entry, L Entry;
		(found?, l, i, j) := search(t, k);
		found? => { assert(~empty? l); [value first l] }
		failed;
	}

	-- to be used only when k appears in t
	apply(t:%, k:K):V == {
		import from Boolean, Entry, L Entry;
		(found?, l, i, j) := search(t, k);
		assert(found?); assert(~empty? l);
		value first l;
	}

	-- returns (found?, l, i, j) where
	--   i = index of l in the table
	--   j = position of l in t.tab.i (i.e. l points to t.tab.i.j)
	--   l points to the key k if found? is false,
	--            to the last element of t.tab.i otherwise (could be empty)
	local search(t:%, k:K):(Boolean, L Entry, Z, Z) == {
		import from Entry, A L Entry;
		i := index(t, k);
		j := 0;
		l := htable(t).i;
		chase := l;
		while ~empty? l repeat {
			j := next j;
			k = key first l => return (true, l, i, j);
			chase := l;
			l := rest l;
		}
		(false, chase, i, j);
	}

	-- return the number of actual entries in the table
	local entries(t:%):Z == {
		import from L Entry, A L Entry;
		n:Z := 0;
		for l in htable t repeat n := n + #l;
		n;
	}

	if K has SerializableType and V has SerializableType then {
		(p:BinaryWriter) << (t:%):BinaryWriter == {
			import from Z, K, V, Entry, L Entry, A L Entry;
			n := entries t;
			p := p << size t << n;
			for l in htable t repeat for e in l repeat
				p := p << key e << value e;
			p;
		}

		<< (p:BinaryReader):% == {
			import from Z, K, V;
			local k:K;
			t := table(<< p);
			n:Z := << p;
			for i in 1..n repeat { k := << p; t.k := << p }
			t;
		}
	}

	if K has InputType and V has InputType then {
		<< (p:TextReader):% == {
			import from Ch, Z, K, V;
			local c:Ch;
			local k:K;
			err := table 1;
			while space?(c := << p) repeat {};
			c ~= leftBracket => err;
			t := table(<< p);
			while space?(c := << p) repeat {};
			while c = comma repeat {
				while space?(c := << p) repeat {};
				c ~= leftBracket => return err;
				k := << p;
				while space?(c := << p) repeat {};
				c ~= comma => return err;
				t.k := << p;
				while space?(c := << p) repeat {};
				c ~= rightBracket => return err;
				while space?(c := << p) repeat {};
			}
			c = rightBracket => t;
			push!(c, p);
			err;			-- syntax error
		}
	}

	if K has OutputType and V has OutputType then {
		(p:TextWriter) << (t:%):TextWriter == {
			import from Boolean, String, Z, K, V;
			import from Entry, L Entry, A L Entry;
			p := p << "[" << size t;
			for l in htable t repeat for e in l repeat
				p := p << ",[" << key e <<","<< value e << "]";
			p << "]";
		}
	}
}
