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
----------------------------- sal_binpow.as ----------------------------------
--
-- This file provides binary powering for arithmetic systems
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

#if ALDOC
\thistype{BinaryPowering}
\History{Manuel Bronstein}{22/11/94}{created}
\History{Manuel Bronstein}{7/9/98}{added small characteristic method}
\Usage{import from \this(T, Z)}
\Params{
{\em T} & \astype{ArithmeticType} & An arithmetic system\\
{\em Z} & \astype{IntegerType} & An integer--like type\\
}
\Descr{\this~provides binary exponentiation of elements of $T$
with exponents in $Z$.}
\begin{exports}
\asexp{binaryExponentiation}: & (T, Z) $\to$ T & Binary powering\\
\asexp{binaryExponentiation!}: & (T, Z) $\to$ T & In--place binary powering\\
\end{exports}
#endif

BinaryPowering(T:ArithmeticType, Z:IntegerType): with {
	binaryExponentiation: (T, Z) -> T;
	binaryExponentiation!: (T, Z) -> T;
#if ALDOC
\aspage{binaryExponentiation}
\Usage{\name(a, n)\\ \name!(a, n)}
\Signature{(T, Z)}{T}
\Params{
{\em a} & T & The element to exponentiate\\
{\em n} & Z & The exponent\\
}
\Retval{Returns $a^n$. The exponent $n$ must be nonnegative.
When using \name!($a, n$),
the storage used by a and n is allowed
to be destroyed or reused, so a and n are lost after this call.}
\Remarks{A call to \name!($a, n$) may cause a and n to be destroyed,
so do not use it unless a and n have been locally allocated,
and are guaranteed not to share space
with other elements. Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
#endif
} == add {
	local m1:MachineInteger			== { import from Z; machine(-1)}
	binaryExponentiation!(a:T, b:Z):T	== binPow!(1, a, b);

	if T has CopyableType and Z has CopyableType then {
		binaryExponentiation(a:T, b:Z):T == binPow!(1, copy a, copy b);
	}
	else {
		binaryExponentiation(a:T, b:Z):T == {
			assert(b >= 0);
			zero? a or one? a => a;
			u:T := 1;
			while b > 0 repeat {
				if bit?(b, 0) then {
					zero?(u := u * a) => return u;
				}
				-- don't use in-place shift if not CopyableType
				if (b := shift(b, m1)) > 0 then {
					one?(a := a * a) => return u;
				}
			}
			u;
		}
	}

	-- returns u a^n, trashes u, a and b
	local binPow!(u:T, a:T, b:Z):T == {
		assert(b >= 0);
		zero? a or one? a => a;
		while b > 0 repeat {
			if bit?(b, 0) then {
				zero?(u := times!(u, a)) => return u;
			}
			if (b := shift!(b, m1)) > 0 then {
				one?(a := times!(a, a)) => return u;
			}
		}
		u;
	}
}

