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
------------------------------- sit_bits.as ----------------------------------
--
-- Bit-arrays
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "salli"

#if ALDOC
\thistype{Bits}
\History{Manuel Bronstein}{12/6/98}{created}
\Usage{import from \this}
\Descr{\this~is a type whose elements are arrays of bits, which can be used
as sets of flags. The implementation is more compact than arrays of boolean
values, but the functionality is the same.}
\begin{exports}
\asexp{apply}:  & (\%, Z) $\to$ \astype{Boolean} & test a bit\\
\asexp{dimension}: & (\%, Z) $\to$ Z & number of true bits\\
\asexp{false}: & Z $\to$ \% & create a set of false bits\\
\asexp{set!}: & (\%, Z, \astype{Boolean}) $\to$ \astype{Boolean} & set a bit\\
\asexp{true}: & Z $\to$ \% & create a set of true bits\\
\end{exports}
\begin{aswhere}
Z &==& \astype{MachineInteger}\\
\end{aswhere}
#endif

macro {
	ARR == PrimitiveMemoryBlock;
	Z == MachineInteger;
}

Bits: with {
	apply: (%, Z) -> Boolean;
#if ALDOC
\aspage{apply}
\Usage{b n\\\name(b, n)}
\Signature{(\%, \astype{MachineInteger})}{\astype{Boolean}}
\Params{
{\em b} & \% & A set of bits\\
{\em n} & \astype{MachineInteger} & An index\\
}
\Retval{Returns the value of the $\sth{n}$ bit of $b$,
the first index being $1$.}
#endif
	dimension: (%, Z) -> Z;
#if ALDOC
\aspage{dimension}
\Signature{(\%, \astype{MachineInteger})}{\astype{MachineInteger}}
\Usage{\name(b, n)}
\Params{
{\em b} & \% & A set of bits\\
{\em n} & \astype{MachineInteger} & An index\\
}
\Retval{Returns the number of bits of index between 1 and $n$ that are true.}
#endif
	false: Z -> %;
	true: Z -> %;
#if ALDOC
\aspage{false,true}
\astarget{false}
\astarget{true}
\Usage{false~n\\ true~n}
\Signature{\astype{MachineInteger}}{\%}
\Params{ {\em n} & \astype{MachineInteger} & The number of bits to create\\ }
\Retval{false($n$) (resp.~true($n$)) returns an array of $n$ bits, all set to
\false (resp.~\true).}
#endif
	set!: (%, Z, Boolean) -> Boolean;
#if ALDOC
\aspage{set!}
\Usage{b.n := v\\\name(b, n, v)}
\Signature{(\%, \astype{MachineInteger}, \astype{Boolean})}{\astype{Boolean}}
\Params{
{\em b} & \% & A set of bits\\
{\em n} & \astype{MachineInteger} & An index\\
{\em v} & \astype{Boolean} & A binary value\\
}
\Retval{Sets the $\sth{n}$ bit of $b$ to $v$ and returns $v$,
the first index being $1$.}
#endif
} == add {
	Rep == ARR;
	import from Rep;

	false(n:Z):%		== bits(n, 0);
	true(n:Z):%		== bits(n, -1);
	local page(n:Z):Z	== next shift(prev n, -3);
	local index(n:Z):Z	== prev(n) /\ 7;

	local bits(n:Z, m:Z):%	== {
		import from Byte;
		per new(page n, lowByte m);
	}

	apply(b:%, n:Z):Boolean	== {
		import from Byte;
		bit?(rep(b)(page n)::Z, index n);
	}

	set!(b:%, n:Z, v?:Boolean):Boolean == {
		import from Byte;
		p := page n;
		a := rep(b)(p)::Z;
		m := index n;
		aa := { v? => set(a, m); clear(a, m); }
		rep(b)(p) := lowByte aa;
		v?
	}

	dimension(b:%, n:Z):Z == {
		m:Z := 0;
		for i in 1..n repeat if b.i then m := next m;
		m;
	}
}
