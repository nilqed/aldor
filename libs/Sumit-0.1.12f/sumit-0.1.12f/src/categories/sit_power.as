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
------------------------------- sit_power.as ----------------------------------
--
-- This file provides pth-powering for rings of finite characteristic
--
-- This type must be included inside "sit_charp.as" to be compiled,
-- but is in a separate file for documentation purposes.
--
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#if ALDOC
\thistype{PthPowering}
\History{Manuel Bronstein}{22/11/94}{created}
\History{Manuel Bronstein}{7/9/98}{added small characteristic method}
\Usage{import from \this~R}
\Params{
{\em R} & \astype{FiniteCharacteristic} & A finite characteristic ring\\
}
\Descr{\this~provides efficient exponentiation of elements of $R$.}
\begin{exports}
\asexp{pExponentiation}: & (T, \astype{Integer}) $\to$ T & $\sth p$--powering\\
\asexp{pExponentiation!}:
& (T, \astype{Integer}) $\to$ T & In--place $\sth p$--powering\\
\end{exports}
#endif

PthPowering(R:FiniteCharacteristic): with {
	pExponentiation: (R, Z) -> R;
	pExponentiation!: (R, Z) -> R;
#if ALDOC
\aspage{pExponentiation}
\astarget{\name!}
\Usage{\name(a, n)\\ \name!(a, n)}
\Signature{(R, \astype{Integer})}{R}
\Params{
{\em a} & R & The element to exponentiate\\
{\em n} & \astype{Integer} & The exponent\\
}
\Retval{Returns $a^n$. The exponent $n$ must be nonnegative.
When using \name!($a, n$),
the storage used by a is allowed
to be destroyed or reused, so a is lost after this call.}
\Remarks{A call to \name!($a, n$) may cause a to be destroyed,
so do not use it unless a has been locally allocated,
and is guaranteed not to share space
with other elements. Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
#endif
} == add {
	local char:Z			== characteristic$R;
	local small?:Boolean		== char < 10008;

	-- buffer.i := a^i for 0 < i < char
	local buffer:Array R == {
		import from MZ;
		small? => new machine char;
		empty;
	}

	if R has CopyableType then {
		pExponentiation(a:R, b:Z):R == pExponentiation!(copy a, b);
	}
	else {
		pExponentiation(a:R, b:Z):R == {
			import from BinaryPowering(R, Z);
			assert(b >= 0);
			zero? b => 1;
			zero? a or one? a => a;
			small? => {
				buffer.1 := a;
				cachedPower(a, b, 1);
			}
			u:R := 1;
			-- a^(p q + r) = (a^p)^q a^r where p == characteristic
			while b > 0 repeat {
				(b, r) := divide(b, char);
				if r > 0 then {
					u := u * binaryExponentiation(a, r);
					zero? u => return u;
				}
				if b > 0 then {
					one?(a := pthPower a) => return u;
				}
			}
			u;
		}

		-- for small p only, buffer.i = a^i for 1 <= i <= m
		-- destroys a and the buffer above m
		local cachedPower(a:R, n:Z, m:MZ):R == {
			assert(n > 0);
			-- a^(p q + r) = (a^q)^p a^r where p == characteristic
			(n, r) := divide(n, char);
			s := machine r;
			if s > m then {
				for i in m..prev s repeat
					buffer(next i) := a * buffer.i;
				m := s;
			}
			zero? n => buffer.s;
			a := pthPower cachedPower(a, n, m);
			zero? s => a;
			a * buffer.s;
		}
	}

	-- destroys a
	-- needs a conditional version for fields later (n < 0)
	pExponentiation!(a:R, b:Z):R == {
		import from BinaryPowering(R, Z);
		import from MZ;
		assert(b >= 0);
		zero? b => 1;
		zero? a or one? a => a;
		small? => {
			buffer.1 := a;
			cachedPower!(a, b, 1);
		}
		u:R := 1;
		while b > 0 repeat {
			-- a^(p q + r) = (a^p)^q a^r where p == characteristic
			(b, r) := divide(b, char);
			if r > 0 then {
				u := times!(u, binaryExponentiation(a, r));
				zero? u => return u;
			}
			if b > 0 then {
				one?(a := pthPower! a) => return u;
			}
		}
		u;
	}

	-- for small p only, buffer.i = a^i for 1 <= i <= m
	-- destroys a and the buffer above m
	local cachedPower!(a:R, n:Z, m:MZ):R == {
		assert(n > 0);
		-- a^(p q + r) = (a^q)^p a^r where p == characteristic
		(n, r) := divide(n, char);
		s := machine r;
		if s > m then {
			for i in m..prev s repeat buffer(next i) := a*buffer.i;
			m := s;
		}
		zero? n => buffer.s;
		a := pthPower! cachedPower!(a, n, m);
		zero? s => a;
		times!(a, buffer.s);
	}
}

