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
------------------------------- pthpower.as ----------------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1994
--
-- This type must be included inside "CATfinring.as" to be compiled,
-- but is in a separate file for documentation purposes.

macro I == SingleInteger;

#if ASDOC
\thistype{PthPowering}
\History{Manuel Bronstein}{22/11/94}{created}
\History{Manuel Bronstein}{7/9/98}{added small characteristic method}
\Usage{import from \this~R}
\Params{ {\em R} & FiniteCharacteristic & A ring of positive characteristic\\ }
\Descr{\this~provides efficient exponentiation in rings of finite
characteristic.}
\begin{exports}
power: & (R, R, Integer) $\to$ R & Fast exponentiation\\
power!: & (R, R, Integer) $\to$ R & Fast exponentiation\\
\end{exports}
#endif

PthPowering(R:FiniteCharacteristic): with {
	power: (R, Integer) -> R;
#if ASDOC
\aspage{power}
\Usage{\name(a, n)}
\Signature{(R, Integer)}{R}
\Params{
{\em a} & R & The element to exponentiate\\
{\em n} & Integer & The exponent ($n \ge 0$)\\
}
\Retval{Returns $a^n$. The exponent $n$ must be nonnegative.}
\seealso{power!(\this)}
#endif
	power!: (R, Integer) -> R;
#if ASDOC
\aspage{power}
\Usage{\name(a, n)}
\Signature{(R, Integer)}{R}
\Params{
{\em u} & R & The coefficient\\
{\em a} & R & The element to exponentiate\\
{\em n} & Integer & The exponent ($n \ge 0$)\\
}
\Retval{Returns $a^n$. The exponent $n$ must be nonnegative.
The storage used by a is allowed
to be destroyed or reused, so a is lost after this call.}
\Remarks{This function may cause a to be destroyed,
so do not use it unless a has been locally allocated,
and is guaranteed not to share space
with other elements. Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
\seealso{power(\this)}
#endif
} == add {
	local char:Integer		== characteristic$R;
	local small?:Boolean		== char < 10008;
	power(a:R, n:Integer):R 	== power!(copy a, n);

	local buffer:PrimitiveArray R == {
		import from I;
		new(small? => prev retract char; 1);
	}

	-- Needs a conditional version for fields later (n < 0)
	-- destroys a
	power!(a:R, n:Integer):R == {
		import from I;
		ASSERT(n >= 0);
		zero? n => 1;
		small? => {
			buffer.1 := a;
			power!(a, n, 1);
		}
		u:R := 1;
		while (~one? a) and (n > 0) repeat {
			-- a^(p q + r) = (a^p)^q a^r where p == characteristic
			(q, r) := divide(n, char);
			u := binpow!(u, copy a, r);
			if (n := q) > 0 then a := pthPower! a;
		}
		u;
	}

	-- for small characteristic only, buffer.i = a^i for 1 <= i <= m
	-- destroys a and the buffer above m
	local power!(a:R, n:Integer, m:I):R == {
		ASSERT(n > 0);
		-- a^(p q + r) = (a^q)^p a^r where p == characteristic
		(q, r) := divide(n, char);
		s := retract r;
		if s > m then {
			for i in m..prev s repeat buffer(next i) := a*buffer.i;
			m := s;
		}
		zero? q => buffer.s;
		a := pthPower! power!(a, q, m);
		zero? s => a;
		times!(a, buffer.s);
	}

	-- returns u a^n, trashes u and a
	local binpow!(u:R, a:R, n:Integer):R == {
		ASSERT(n >= 0);
		ASSERT(n < char);
		while (~one? a) and (n > 0) repeat {
			-- a^(2 q + r) = (a^2)^q a^r
			(q, r) := divide(n, 2);
			if r = 1 then u := times!(u, a);
			if (n := q) > 0 then a := times!(a, a);
		}
		u;
	}
}
