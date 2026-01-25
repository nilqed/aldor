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
---------------------- sit_pring.as -----------------------------
--
-- Partial rings, i.e. rings where operations are allowed to fail
--
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"

macro {
	Z	== Integer;
	U	== Partial %;
}

#if ALDOC
\thistype{PartialRing}
\History{Manuel Bronstein}{10/01/96}{created}
\Usage{\this: Category}
\Descr{\this~is the category of rings where all the arithmetic operations
are partial, \ie~they are allowed to fail. Typical examples are matrices
of different sizes, or unions of several true rings.}
\begin{exports}
\asexp{0}: & \% & Additive identity\\
\asexp{1}: & \% & Multiplicative identity \\
\asexp{-}: &  \% $\to$ \astype{Partial} \% & Negation \\
\asexp{-}: &  (\%, \%) $\to$ \astype{Partial} \% & Substraction \\
\asexp{+}: &  (\%, \%) $\to$ \astype{Partial} \% & Addition \\
\asexp{$\ast$}: &  (\%, \%) $\to$ \astype{Partial} \% & Multiplication \\
\asexp{/}: &  (\%, \%) $\to$ \astype{Partial} \% & Exact division \\
\asexp{\^{}}: &  (\%, \%) $\to$ \astype{Partial} \% & Exponentiation \\
\asexp{<}: &  (\%, \%) $\to$ \astype{Partial} \% & Comparison \\
\asexp{>}: &  (\%, \%) $\to$ \astype{Partial} \% & Comparison \\
\asexp{$\le$}: &  (\%, \%) $\to$ \astype{Partial} \% & Comparison \\
\asexp{$\ge$}: &  (\%, \%) $\to$ \astype{Partial} \% & Comparison \\
\asexp{$[]$}:
& \builtin{Tuple} \% $\to$ \astype{Partial} \% & Construct a structure\\
\asexp{coerce}:
& \astype{Boolean} $\to$ \% & Convert a boolean to a ring element\\
\asexp{coerce}:
&  \astype{Integer} $\to$ \% & Convert an integer to a ring element\\
\asexp{integer}:
& \% $\to$ \astype{Partial} \astype{Integer} & Convert to an integer\\
\asexp{product}: &  List \% $\to$ \astype{Partial} \% & Multiplication \\
\asexp{sum}: &  List \% $\to$ \astype{Partial} \% & Addition \\
\end{exports}
#endif

define PartialRing: Category == SumitType with {
	0:%;
	1:%;
	-: % -> U;
	-: (%, %) -> U;
	+: (%, %) -> U;
	*: (%, %) -> U;
	/: (%, %) -> U;
	^: (%, %) -> U;
	<: (%, %) -> U;
	>: (%, %) -> U;
	<=: (%, %) -> U;
	>=: (%, %) -> U;
	coerce: Boolean -> %;
	coerce: Z -> %;
	integer: % -> Partial Z;
	list: List % -> U;
	product: List % -> U;
	sum: List % -> U;
	default {
		0:%			== { import from Z; 0 :: % }
		1:%			== { import from Z; 1 :: % }
		sum(l:List %):U		== partialReduce(+, l, 0);
		product(l:List %):U	== partialReduce(*, l, 1);
		coerce(b?:Boolean):%	== { b? => 1; 0 }
		list(l:List %):U	== failed;

		(a:%) <= (b:%):U == {
			import from Boolean;
			a = b => [true::%];
			a < b;
		}

		(a:%) >= (b:%):U == {
			import from Boolean;
			a = b => [true::%];
			a > b;
		}

		(a:%) > (b:%):U == {
			import from Boolean;
			a = b => [false::%];
			failed?(u := a < b) => u;
			[(0 = retract u)::%];
		}

		-- default is that only the integers are ordered
		(a:%) < (b:%):U == {
			import from Boolean, Z, U, Partial Z;
			a = b => [false::%];
			failed?(u := integer a)
				or failed?(v := integer b) => failed;
			[(retract u < retract v)::%];
		}

		local partialReduce(op: (%, %) -> U, l:List %, def:%):U == {
			import from Boolean;
			empty? l => [def];
			x := first l;
			while ~empty?(l := rest l) repeat {
				failed?(u := op(x, first l)) => return failed;
				x := retract u;
			}
			[x];
		}

		(a:%) - (b:%):U == {
			failed?(u := -b) => u;
			a + retract u;
		}
	}
}
