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
-------------------------- sit_integer.as ---------------------------------
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{IntegerCategory}
\History{Manuel Bronstein}{23/5/95}{created}
\Usage{\this: Category}
\Descr{ \this~is the category of integer-like rings.}
\begin{exports}
\category{\astype{CharacteristicZero}}\\
\category{\astype{EuclideanDomain}}\\
\category{\astype{IntegerType}}\\
\category{\astype{Parsable}}\\
\category{\astype{Specializable}}\\
\asexp{integer}: & \% $\to$ \astype{Integer} & Conversion to an integer\\
\end{exports}
#endif

define IntegerCategory: Category ==
	Join(IntegerType, CharacteristicZero, EuclideanDomain,
		Specializable, Parsable) with{
			binomial: (%, %) -> %;
#if ALDOC
\aspage{binomial}
\Usage{\name(n, m)}
\Signature{(\%,\%)}{\%}
\Params{ {\em n,m} & \% & Integers\\}
\Retval{Returns
$$
{n \choose m} = \frac{n!}{m! (n-m)!}\,.
$$
Returns $0$ if either $m < 0$ or $n < m$.}
#endif
			integer: % -> Integer;
#if ALDOC
\aspage{integer}
\Usage{\name~n}
\Signature{\%}{\astype{Integer}}
\Params{ {\em n} & \% & An integer\\}
\Retval{Returns n as an integer.}
#endif
	default {
		canonicalUnitNormal?:Boolean	== true;
		karatsubaCutoff:MachineInteger	== 12;
		euclideanSize(n:%):Integer	== integer abs n;
		relativeSize(n:%):MachineInteger== { zero? n => 0; length n }
			
		-- the following is necessary because rem is balanced otherwise
		remainder!(a:%, b:%):%		== a mod b;

		-- returns (y, u, u^{-1}) s.t. x = u y
		unitNormal(x:%):(%, %, %) == {
			sign(x) < 0 => (-x,-1,-1);
			(x, 1, 1)
		};

		-- returns (y, u^{-1} z) s.t. x = u y
		-- TEMPORARY: CANNOT OVERLOAD (BUG 1272)
		-- unitNormal(x:%, z:%):(%, %) == {
		unitNormalize(x:%, z:%):(%, %) == {
			import from MachineInteger;
			sign(x) < 0 => (-x,-z);
			(x, z)
		}

		binomial(n:%, m:%):% == {
			m < 0 or n < m => 0;
			if m < n - m then m := n - m;
			assert(m >= n - m);
			n = m => 1;
			denom := factorial(n - m);
			numer:% := 1;
			while m < n repeat numer := times!(numer, m := next m);
			assert zero?(numer rem denom);
			quotient(numer, denom);
		}

		extree(x:%):ExpressionTree == {
			import from ExpressionTreeLeaf;
			extree leaf integer x;
		}

		eval(t:ExpressionTreeLeaf):Partial % == {
			import from Integer;
			machineInteger? t => [machineInteger(t)::Integer::%];
			integer? t => [integer(t)::%];
			failed;
		}

		eval(op:MachineInteger, l:List ExpressionTree):Partial % == {
			import from ParsingTools %;
			evalArith(op, l);
		}

		exactQuotient(x:%, y:%):Partial % == {
			(q, r) := divide(x, y);
			zero? r => [q];
			failed
		}

		specialization(Image:CommutativeRing):_
			PartialFunction(%, Image) == {
			partialFunction((n:%):Boolean +-> true,
					(n:%):Image +-> integer(n)::Image);
		}

		-- MORE EFFICIENT THAT THE GENERAL DEFAULT
		unit?(x:%):Boolean == one? x or x = -1;
	}
};

extend AldorInteger: IntegerCategory == add {
#if DEBUG
	-- Those 2 assume that Integer == AldorInteger
	integer(u:%):Integer		== u;
	coerce(n:Integer):%		== n;
#else
	-- This assumes that Integer == GmpInteger
	integer(u:%):Integer		== u::Integer;
	coerce(n:Integer):%		== coerce(n)$Integer;
#endif

	-- TEMPORARY: THOSE 6 DEFAULTS ARE NOT TAKEN FROM IntegerCategory!!!
	canonicalUnitNormal?:Boolean	== true;
	karatsubaCutoff:MachineInteger	== 12;
	relativeSize(n:%):MachineInteger== { zero? n => 0; length n }
	unit?(x:%):Boolean		== one? x or x = -1;
	unitNormal(x:%):(%, %, %) == {
		import from MachineInteger;
		sign(x) < 0 => (-x,-1,-1);
		(x, 1, 1)
	};
	-- TEMPORARY: CANNOT OVERLOAD (BUG 1272)
	-- unitNormal(x:%, z:%):(%, %) == {
	unitNormalize(x:%, z:%):(%, %) == {
		import from MachineInteger;
		sign(x) < 0 => (-x,-z);
		(x, z)
	}

	-- TEMPORARY: THOSE CANNOT BE DEFINED AS DEFAULTS
	-- AS LONG AS THE COMPILER DOES EARLY-BINDING IN OTHER DEFAULTS
	divide!(a:%, b:%, q:%):(%, %)	== divide(a, b);
	remainder!(a:%, b:%):%		== a rem b;
}

