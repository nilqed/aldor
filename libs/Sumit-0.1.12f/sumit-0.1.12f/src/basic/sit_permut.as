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
----------------------- sit_permut.as -----------------------------
--
-- Permutations of a finite numbe of elements
--
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	Z == MachineInteger;
	A == PrimitiveArray;
}

#if ALDOC
\thistype{Permutation}
\History{Manuel Bronstein}{9/12/1999}{created}
\Usage{import from \this~n}
\Params{{\em n} & \astype{MachineInteger} & The number of elements\\}
\Descr{\this(n) implements the group of permutations on $n$ elements.}
\begin{exports}
\category{\astype{CopyableType}}\\
\category{\astype{Group}}\\
\asexp{apply}: & (\%, \astype{MachineInteger}) $\to$ \astype{MachineInteger} &
Image of an element\\
\asexp{mapping}:
& \% $\to$ (\astype{MachineInteger} $\to$ \astype{MachineInteger}) &
Action of a permutation\\
\asexp{sign}: & \% $\to$ \astype{MachineInteger} & Sign\\
\asexp{transpose}:
& (\astype{MachineInteger}, \astype{MachineInteger}) $\to$ \% & Transposition\\
\asexp{transpose!}:
& (\%, \astype{MachineInteger}, \astype{MachineInteger}) $\to$ \% &
Compose with a transposition\\
\end{exports}
#endif

Permutation(n:Z):Join(CopyableType, Group) with {
	apply: (%, Z) -> Z;
#if ALDOC
\aspage{apply}
\Usage{ \name($\sigma$, x) \\ $\sigma x$}
\Signature{(\%, \astype{MachineInteger})}{\astype{MachineInteger}}
\Params{
{\em $\sigma$} & \% & A permutation\\
{\em x} & \astype{MachineInteger} & An index\\
}
\Retval{Returns $\sigma x$.}
#endif
	mapping: % -> (Z -> Z);
#if ALDOC
\aspage{mapping}
\Usage{\name~$\sigma$}
\Signature{\%}{(\astype{MachineInteger} $\to$ \astype{MachineInteger})}
\Params{ {\em $\sigma$} & \% & A permutation\\ }
\Retval{Returns the map corresponding to $\sigma$.}
\seealso{\asexp{apply}}
#endif
	sign: % -> Z;
#if ALDOC
\aspage{sign}
\Usage{\name~$\sigma$}
\Signature{\%}{\astype{MachineInteger}}
\Params{ {\em $\sigma$} & \% & A permutation\\ }
\Retval{Returns the sign of $\sigma$, \ie $(-1)^\epsilon$
where $\epsilon$ is the number of tranpositions in the factorization
of $\sigma$.}
#endif
	transpose: (Z, Z) -> %;
	transpose!: (%, Z, Z) -> %;
#if ALDOC
\aspage{transpose}
\astarget{\name!}
\Usage{\name(x,y)\\ \name!($\sigma$,x,y)}
\Signatures{
\name: & (\astype{MachineInteger}, \astype{MachineInteger}) $\to$ \%\\
\name!: & (\%, \astype{MachineInteger}, \astype{MachineInteger}) $\to$ \%\\
}
\Params{
{\em $\sigma$} & \% & A permutation\\
{\em x,y} & \astype{MachineInteger} & Indices\\
}
\Retval{\name(x,y) returns the transposition $(x y)$, while
\name!($\sigma$,x,y) replaces $\sigma$ by the composition $(x y) \circ \sigma$
and returns it.}
\Remarks{\name!~does not make a copy of $\sigma$, but performs all the
computations in--place, storing the final result in $\sigma$. Also, it
does not create the transposition $(x y)$.}
#endif
} == {
	assert(n >= 0);
	add {
	Rep == A Z;	-- rep(s).i == s.i for i > 0, rep(s).0 = sign(s)

	local newperm():%		== { import from Rep; per new next n; }
	local setsign!(s:%, e:Z):Z	== { import from Rep; rep(s).0 := e; }
	sign(s:%):Z			== { import from Rep; rep(s).0 }
	mapping(s:%):Z -> Z		== { (i:Z):Z +-> s i }

	(s:%) = (t:%):Boolean == {
		import from Z;
		for i in 1..n repeat {
			s.i ~= t.i => return false;
		}
		true;
	}

	extree(s:%):ExpressionTree == {
		import from Z, List ExpressionTree;
		ExpressionTreeList [extree(s i) for i in 1..n];
	}

	apply(s:%, i:Z):Z == {
		import from Rep;
		assert(i > 0); assert(i <= n);
		rep(s).i;
	}

	local set!(s:%, i:Z, j:Z):Z == {
		import from Rep;
		assert(i > 0); assert(i <= n);
		assert(j > 0); assert(j <= n);
		rep(s).i := j;
	}

	copy(s:%):% == {
		import from Z;
		s0 := newperm();
		setsign!(s0, sign s);
		for i in 1..n repeat s0.i := s i;
		s0;
	}

	local ident():% == {
		import from Z;
		s := newperm();
		setsign!(s, 1);
		for i in 1..n repeat s.i := i;
		s;
	}
	1:% == ident();

	transpose(i:Z, j:Z):% == {
		assert(i > 0); assert(i <= n);
		assert(j > 0); assert(j <= n);
		i = j => 1;
		s := ident();
		setsign!(s, -1);
		s.i := j;
		s.j := i;
		s;
	}

	-- replaces s by (i j) s
	transpose!(s:%, i:Z, j:Z):% == {
		assert(i > 0); assert(i <= n);
		assert(j > 0); assert(j <= n);
		i = j => s;
		setsign!(s, -sign s);
		t := s.i;
		s.i := s.j;
		s.j := t;
		s;
	}

	inv(s:%):% == {
		import from Z;
		one? s => s;
		s1 := newperm();
		setsign!(s1, sign s);
		for i in 1..n repeat s1(s i) := i;
		s1;
	}

	(s:%) / (t:%):% == {
		import from Z;
		one? t => s;
		st := newperm();
		setsign!(st, sign(s) * sign(t));
		for i in 1..n repeat st(t i) := s i;
		st;
	}

	(s:%) * (t:%):% == {
		import from Z;
		st := newperm();
		setsign!(st, sign(s) * sign(t));
		for i in 1..n repeat st.i := s t i;
		st;
	}

	(s:%) ^ (m:Integer):% == {
		import from Z;
		zero? m => 1;
		one? m => s;
		m < 0 => inv(s)^(-m);
		sm := copy s;
		sgn:Z := { sign(s) > 0 or even? m => 1; -1 }
		setsign!(sm, sgn);
		for i in 2..m repeat sm := times!(sm, s);
		sm;
	}
	}
}

