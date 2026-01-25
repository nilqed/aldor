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
---------------------------- sal_partial.as ---------------------------------
--
-- This file defines a partial T, i.e. a union of T and failed.
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
\thistype{Partial}
\History{Manuel Bronstein}{7/10/98}{created}
\Usage{import from \this~T}
\Params{ {\em T} & Type & a type\\}
\Descr{\this(T) implements a union of T and \failed.}
\begin{exports}
\asexp{[]}: & T $\to$ \% & create an element\\
\asexp{failed}: & \% & the element \failed\\
\asexp{failed?}: & \% $\to$ \astype{Boolean} & check for the element \failed\\
\asexp{retract}: & \% $\to$ T & convert to an element of T\\
\end{exports}
\begin{exports}[if $T$ has \astype{PrimitiveType} then]
\category{\astype{PrimitiveType}}\\
\end{exports}
\begin{exports}[if $T$ has \astype{HashType} then]
\category{\astype{HashType}}\\
\end{exports}
\begin{exports}[if $T$ has \astype{InputType} then]
\category{\astype{InputType}}\\
\end{exports}
\begin{exports}[if $T$ has \astype{OutputType} then]
\category{\astype{OutputType}}\\
\end{exports}
\begin{exports}[if $T$ has \astype{SerializableType} then]
\category{\astype{SerializableType}}\\
\end{exports}
#endif

Partial(T:Type): with {
	if T has PrimitiveType then PrimitiveType;
	if T has InputType then InputType;
	if T has OutputType then OutputType;
	if T has SerializableType then SerializableType;
	bracket: T -> %;
#if ALDOC
\aspage{[]}
\Usage{[t]}
\Signature{T}{\%}
\Params{{\em t} & T & an element\\ }
\Retval{Returns the element t converted to an element of \%.}
#endif
	failed: %;
	failed?: % -> Boolean;
#if ALDOC
\aspage{failed}
\astarget{\name?}
\Usage{\name\\ \name?~x}
\Signatures{
\name: & \%\\
\name?: & \% $\to$ \astype{Boolean}\\
}
\Params{{\em x} & \% & a partial element\\ }
\Retval{\name~returns the special element \failed, while \name?(x) returns
\true if x is \failed, \false otherwise.}
#endif
	retract: % -> T;
#if ALDOC
\aspage{retract}
\Usage{\name~x}
\Signature{\%}{T}
\Params{{\em x} & \% & a partial element\\ }
\Retval{Returns the element x converted to an element of T, provided that
x is not \failed.}
#endif
} == add {
	macro {
		Ptr == Pointer;
		Rep == Record(val:T);
	}
	import from Rep;

	failed:%		== { import from Ptr; nil pretend % };
	failed?(x:%):Boolean	== { import from Ptr; nil?(x pretend Ptr); }
	[x:T]:%			== per [x];
	local leftBracket:Ch	== { import from Z; char 91; }
	local rightBracket:Ch	== { import from Z; char 93; }

	retract(x:%):T 	== {
		import from Boolean;
		assert(~failed? x);
		rep(x).val;
	}

	if T has PrimitiveType then {
		(x:%) = (y:%):Boolean == {
			import from T;
			fy? := failed? y;
			failed? x => fy?;
			~fy? and retract x = retract y;
		}
	}

	if T has HashType then {
		hash(x:%):MachineInteger == {
			import from T;
			failed? x => 0;
			hash retract x;
		}
	}

	if T has OutputType then {
		(p:TextWriter) << (x:%):TextWriter == {
			import from Boolean, Character, T;
			f? := failed? x;
			p << leftBracket << f?;
			if ~f? then p := p << space << retract x;
			p << rightBracket;
		}
	}

	if T has SerializableType then {
		(p:BinaryWriter) << (x:%):BinaryWriter == {
			import from Boolean, T;
			f? := failed? x;
			p := p << f?;
			f? => p;
			p << retract x;
		}

		<< (p:BinaryReader):% == {
			local x:T;
			f?:Boolean := << p;
			if ~f? then x := << p;
			f? => failed;
			[x];
		}
	}

	if T has InputType then {
		<< (p:TextReader):% == {
			import from Boolean, Character, T;
			local c:Character;
			local x:T;
			while space?(c := << p) repeat {};
			c ~= leftBracket => failed;
			f?:Boolean := << p;
			if ~f? then x := << p;
			while space?(c := << p) repeat {};
			assert(c = rightBracket);
			f? => failed;
			[x];
		}
	}
}
