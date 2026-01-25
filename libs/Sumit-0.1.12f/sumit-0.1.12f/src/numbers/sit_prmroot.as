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
---------------------------- sit_prmroot.as ---------------------------------
--
-- Computations of modular primitive roots
--
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{PrimitiveRoots}
\History{Manuel Bronstein}{8/6/95}{created}
\Usage{import from \this}
\Descr{\this~implements functionalities needed to compute generators
of small cyclic groups.}
\begin{exports}
\asexp{factors:} & Z $\to$ \astype{List} Z & List of prime factors\\
\asexp{primitiveRoot:} & Z $\to$ Z & Modular primitive root\\
\end{exports}
\begin{aswhere}
Z & == & \astype{MachineInteger}\\
\end{aswhere}
#endif

macro {
	A	== Array;
	Z	== MachineInteger;
}

PrimitiveRoots: with {
	factors: Z -> List Z;
#if ALDOC
\aspage{factors}
\Usage{\name~n}
\Signature{\astype{MachineInteger}}{\astype{List} \astype{MachineInteger}}
\Params{ {\em n} & \astype{MachineInteger} & An integer\\ }
\Retval{Returns all the prime factors $p$ of $n$ with $1 < d < \abs n$.}
#endif
	primitiveRoot: Z -> Z;
#if ALDOC
\aspage{primitiveRoot}
\Usage{\name~p}
\Signature{\astype{MachineInteger}}{\astype{MachineInteger}}
\Params{ {\em p} & \astype{MachineInteger} & A prime\\ }
\Retval{Returns a generator of the multiplicative group
$(\ZZ/p \ZZ)^\ast$.}
\Remarks{The argument $p$ must be a prime number, otherwise this function
returns any integer with no significance.}
#endif
} == add {
	factors(n:Z):List Z == {
		assert(n >= 0);
		n < 2 => empty;
		even? n => cons(2, reverse! factors1 deflate(n, 2));
		reverse! factors1 n;
	}

	-- for really small odd numbers only! (Very inefficient)
	-- returns the list of factors in decreasing order
	local factors1(n:Z):List Z == {
		assert(odd? n);
		assert(n >= 0);
		l:List Z := empty;
		n < 2 => l;
		i:Z := 3;
		(square?, s) := nthRoot(n, 2);	-- s^2 <= n < (s + 1)^2
		while i <= s repeat {
			zero?(n rem i) => {
				l := cons(i, l);
				n := deflate(n, i);
				(square?, s) := nthRoot(n, 2);
			}
			i := i + 2;
		}
		cons(n, l);
	}

	-- remove all the powers of m from n
	local deflate(n:Z, m:Z):Z == {
		r:Z := 0;
		while zero? r repeat {
			(q, r) := divide(n, m);
			if zero? r then n := q;
		}
		n;
	}

	local primRoot?(n:Z, p:Z, l:List Z):Boolean == {
		for e in l repeat { mod_^(n, e, p) = 1 => return false; }
		true;
	}

	primitiveRoot(p:Z):Z == {
		import from SmallPrimes;
		assert(p > 1);
		p = 2 => 1;
		assert(odd? p);
		p <= maxPrime => primRoot p;
		l := factors(p1 := prev p);
		for j in 2..p1 repeat { primRoot?(j, p, l) => return j; }
		0;
	}
}
