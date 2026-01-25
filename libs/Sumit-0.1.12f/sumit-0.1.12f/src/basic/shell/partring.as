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
---------------------- partring.as -----------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1995
--
#include "sumit"

macro {
	Z	== Integer;
	U	== Partial %;
}

#if ASDOC
\thistype{PartialRing}
\History{Manuel Bronstein}{10/01/96}{created}
\Usage{\this: Category}
\Descr{\this~is the category of rings where all the arithmetic operations
are partial, \ie~they are allowed to fail. Typical examples are matrices
of different sizes, or unions of several true rings.}
\begin{exports}
0: & \% & Additive identity\\
1: & \% & Multiplicative identity \\
-: &  \% $\to$ Partial \% & Negation \\
-: &  (\%, \%) $\to$ Partial \% & Substraction \\
+: &  (\%, \%) $\to$ Partial \% & Addition \\
$\ast$: &  (\%, \%) $\to$ Partial \% & Multiplication \\
/: &  (\%, \%) $\to$ Partial \% & Exact division \\
\^{}: &  (\%, \%) $\to$ Partial \% & Exponentiation \\
<: &  (\%, \%) $\to$ Partial \% & Comparison \\
>: &  (\%, \%) $\to$ Partial \% & Comparison \\
$\le$: &  (\%, \%) $\to$ Partial \% & Comparison \\
$\ge$: &  (\%, \%) $\to$ Partial \% & Comparison \\
coerce: &  Z $\to$ \% & Convert an integer to a ring element\\
integer: & \% $\to$ Partial Z & Convert to an integer\\
product: &  List \% $\to$ Partial \% & Multiplication \\
sum: &  List \% $\to$ Partial \% & Addition \\
\end{exports}
#endif

PartialRing: Category == SumitType with {
	0:%;
	1:%;
	-: % -> U;
	-: (%, %) -> U;
	+: (%, %) -> U;
	*: (%, %) -> U;
	/: (%, %) -> U;
	^: (%, %) -> U;
	coerce: Z -> %;
	integer: % -> Partial Z;
	product: List % -> U;
	sum: List % -> U;
	default {
		0:%			== { import from Z; 0 :: %; }
		1:%			== { import from Z; 1 :: %; }
		sample:%		== 1;
		sum(l:List %):U		== partialReduce(+, l, 0);
		product(l:List %):U	== partialReduce(*, l, 1);
		(a:%) <= (b:%):Partial %== { a = b => [1]; a < b; }
		(a:%) >= (b:%):Partial %== { a = b => [1]; a > b; }

		(a:%) > (b:%):Partial % == {
			failed?(u := a <= b) => u;
			0 = retract u => [1];
			[0];
		}

		(a:%) < (b:%):Partial % == {
			import from Z, Partial Z;
			a = b => [0];
			failed?(u := integer a)
				or failed?(v := integer b) => failed;
			retract u < retract v => [1];
			[0];
		}

		local partialReduce(op: (%, %) -> U, l:List %, def:%):U == {
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
