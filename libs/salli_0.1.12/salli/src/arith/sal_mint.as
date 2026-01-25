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
---------------------------- sal_mint.as ------------------------------------
--
-- Machine integers
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro Z == MachineInteger;

#if ALDOC
\thistype{MachineInteger}
\History{Manuel Bronstein}{28/9/98}{created}
\Usage{import from \this}
\Descr{\this~implements the full-word signed machine integers.}
\begin{exports}
\category{\astype{CopyableType}}\\
\category{\astype{IntegerType}}\\
\asexp{bytes}: & \% & machine word-size\\
\asexp{max}: & \% & largest machine integer\\
\asexp{min}: & \% & smallest machine integer\\
\asexp{mod\_+}: & (\%, \%, \%) $\to$ \% & modular addition\\
\asexp{mod\_-}: & (\%, \%, \%) $\to$ \% & modular substraction\\
\asexp{mod\_*}: & (\%, \%, \%) $\to$ \% & modular multiplication\\
\asexp{mod\_/}: & (\%, \%, \%) $\to$ \% & modular division\\
\asexp{mod\_$\hat{}$}: & (\%, \%, \%) $\to$ \% & modular exponentiation\\
\asexp{modInverse}: & (\%, \%) $\to$ \% & modular inverse\\
\end{exports}

\aspage{bytes,max,min}
\astarget{bytes}
\astarget{max}
\astarget{min}
\Usage{bytes\\max\\min}
\Signature{}{\%}
\Retval{bytes, max and min return respectively the
size in bytes of a machine integer, the largest and the smallest
machine integers.}
#endif

extend MachineInteger: Join(CopyableType, IntegerType) with {
	mod_+: (%, %, %) -> %;
	mod_-: (%, %, %) -> %;
	mod_*: (%, %, %) -> %;
	mod_/: (%, %, %) -> %;
	mod_^: (%, %, %) -> %;
	modInverse: (%, %) -> %;
#if ALDOC
\aspage{mod\_+,mod\_-,mod\_*,mod\_/,mod\_$\hat{}$,modInverse}
\astarget{mod\_+}
\astarget{mod\_-}
\astarget{mod\_*}
\astarget{mod\_/}
\astarget{mod\_$\hat{}$}
\astarget{modInverse}
\Usage{mod\_X(a, b, n)\\ modInverse(a, n)}
\Params{{\em a, b, n} & \% & machine integers\\ }
\Signatures{
mod\_X: & (\%, \%, \%) $\to$ \%\\
modInverse: & (\%, \%) $\to$ \%\\
}
\Retval{mod\_X(a, b, n) returns $(a X b) \pmod n$ where $X$ is one
of $+,-,\ast,/,\hat{}$, while modInverse(a, b) returns the inverse
of $a$ modulo $n$.}
\Remarks{Those operations require that $0 \le a, b < n$.}
#endif
	export from IntegerSegment %;
} == add {

	import from Machine;
	Rep == SInt;

	local halfword:%			== prev shift(1, 4 * bytes);
	local lhalfword:%			== shift(halfword, -1);
	(a:%) + (b:%):%				== per(rep a + rep b);
	(a:%) * (b:%):%				== per(rep a * rep b);
	(a:%) /\ (b:%):%			== per(rep a /\ rep b);
	(a:%) \/ (b:%):%			== per(rep a \/ rep b);
	(a:%) < (b:%):Boolean			== (rep a < rep b)::Boolean;
	~(a:%):%				== per(~ rep a);
	length(a:%):Z				== per length rep a;
	gcd(a:%, b:%):%				== per gcd(rep a, rep b);
	bit?(a:%, b:%):Boolean			== bit(rep a, rep b)::Boolean;
	(a:%) quo (b:%):%			== per(rep a quo rep b);
	(a:%) rem (b:%):%			== per(rep a rem rep b);
	coerce(a:Z):%				== a;
	machine(a:%):Z				== a;
	copy(a:%):%				== a;
	random(n:Z):%				== random();

	-- THOSE ARE BETTER THAN THE CORRESPONDING CATEGORY DEFAULTS
        xor(a:%, b:%):%				== per xor(rep a, rep b);
	(a:%) <= (b:%):Boolean			== (rep a <= rep b)::Boolean;
	zero?(a:%):Boolean			== zero?(rep a)::Boolean;
	(a:%) - (b:%):%				== per(rep a - rep b);
	-(a:%):%				== per(- rep a);
	add!(a:%, b:%):%			== a + b;
	times!(a:%, b:%):%			== a * b;
	next(a:%):%				== per next rep a;
	prev(a:%):%				== per prev rep a;

	-- TEMPORARY (BUG1182) DEFAULTS DON'T INLINE WELL
	(a:%) > (b:%):Boolean == ~(a <= b);
	(a:%) >= (b:%):Boolean == ~(a < b);
	max(a:%, b:%):% == { a < b => b; a };
	min(a:%, b:%):% == { a < b => a; b };
	minus!(a:%):% == - a;
	minus!(a:%, b:%):% == a - b;
	one?(a:%):Boolean == a = 1;
	abs(a:%):% == { a < 0 => -a; a }
	set(a:%, n:Z):% == a \/ shift(1, n);
	clear(a:%, n:Z):% == a /\ ~(shift(1, n));
	hash(a:%):Z == machine a;
	odd?(a:%):Boolean == ~even? a;
	even?(a:%):Boolean == zero?(a /\ 1);
	(a:%) mod (b:%):% == {
		assert(b ~= 0);
		(r := a rem b) < 0 => r + abs b;
		r;
	}

	sign(a:%):% == {
		zero? a => 0;
		a > 0 => 1;
		-1;
	}

	(a:%) ^ (b:%):% == {
		assert(b >= 0);
		zero? a or one? a => a;
		u:% := 1;
		while b > 0 repeat {
			if odd? b then u := u * a;
			if (b := shift(b, -1)) > 0 then a := a * a;
		}
		u;
	}
	
	-- random() will be provided in sal_random.as by an extension
	-- this definition ensures that we can check whether the extended
	-- definition is really used.
	random():% == never;

	divide(a:%, b:%):(%, %)	== {
		(q, r) := divide(rep a, rep b);
		(per q, per r);
	}

	shift(a:%, b:Z):% == {
		b < 0 => per shiftDown(rep a, - rep b);
		per shiftUp(rep a, rep b);
	}

	nthRoot(x:%, e:%):(Boolean, %) == {
		import from IntegerTypeTools %;
		binaryNthRoot(x, e);
	}

	(p:TextWriter) << (x:%):TextWriter == {
		import from IntegerTypeTools %;
		print(x, 10, p);
	}

	<< (p:TextReader):% == {
		import from IntegerTypeTools %;
		scan p;
	}

	-- integers are written in binary low byte first
	-- the length is systematically 8 bytes, regardless of the platform
	(p:BinaryWriter) << (x:%):BinaryWriter == {
		import from Byte, IntegerSegment %;
		for m in 1..8 repeat {
			p := p << lowByte x;
			x := shift(x, -8);
		}
		p;
	}

	-- integers are read in binary low byte first
	-- the length is systematically 8 bytes, regardless of the platform
	<< (p:BinaryReader):% == {
		import from Byte, IntegerSegment %;
		n:% := 0;
		s:% := 0;
		b := lowByte n;
		for m in 0..7 repeat {
			b := << p;
			if m < bytes then {	-- shift is undefined otherwise
				n := n \/ shift(b::%, s);
				s := s + 8;
			}
		}
		n;
	}

	-- the following are taken from Pete Broadbery (axllib)
	mod_+(a:%, b:%, n:%):% == {
		assert(0 <= a); assert(a < n);
		assert(0 <= b); assert(b < n);
		-- Trick to avoid overflow
		a := a - n;
		(c := a + b) < 0 => c + n;
		c;
	}

	mod_-(a:%, b:%, n:%):% == {
		assert(0 <= a); assert(a < n);
		assert(0 <= b); assert(b < n);
		(c := a - b) < 0 => c + n;
		c;
	}

	mod_*(a:%, b:%, n:%):% == {
		assert(0 <= a); assert(a < n);
		assert(0 <= b); assert(b < n);
		a = 1 => b;
		b = 1 => a;
		n < halfword or
			(a < halfword and b < halfword) => (a * b) mod n;
		(nh, nl) := double_*(a pretend Word, b pretend Word);
		(qh, ql, rm) := doubleDivide(nh, nl, n pretend Word);
		rm pretend %;
	}

	-- returns junk if b is not invertible modulo n
	mod_/(a:%, b:%, n:%):% == {
		assert(0 <= a); assert(a < n);
		assert(0 < b); assert(b < n);
		mod_*(a, modInverse(b, n), n);
	}

	-- returns junk if b is not invertible modulo n
	modInverse(b:%, n:%):% == {
		import from Boolean;
		assert(0 < b); assert(b < n);
		(c0:%, d0:%) := (b, n);
		(c1:%, d1:%) := (1, 0);
		while ~zero?(d0) repeat {
			(q, r) := divide(c0, d0);
			(c0, d0) := (d0, r);
			(c1, d1) := (d1, c1 - q * d1);
		}
		assert(c0 = 1);		-- or b is not invertible in Z/nZ
		c1 < 0  => c1 + n;
		c1;
	}

	mod_^(a:%, b:%, n:%):% == {
		assert(0 <= a); assert(a < n);
		b < 0 => mod_^(mod_/(1, a, n), -b, n);
		n < lhalfword => lhmod_^(a, b, n);
		n < halfword => hmod_^(a, b, n);
		u:% := 1;
		while b > 0 repeat {
			if odd? b then u := mod_*(u, a, n);
			a := mod_*(a, a, n);
			b := shift(b, -1);
		}
		u;
	}

	-- this one guarantees that products don't overflow
	local hmod_^(a:%, b:%, n:%):% == {
		assert(0 <= a); assert(a < n); assert(n < halfword);
		assert(0 <= b);
		u:% := 1;
		while b > 0 repeat {
			if odd? b then u := (u * a) mod n;
			a := (a * a) mod n;
			b := shift(b, -1);
		}
		u;
	}

	-- this one guarantees that products don't overflow and remain >= 0
	local lhmod_^(a:%, b:%, n:%):% == {
		assert(0 <= a); assert(a < n); assert(n < lhalfword);
		assert(0 <= b);
		u:% := 1;
		while b > 0 repeat {
			if odd? b then u := (u * a) rem n;
			a := (a * a) rem n;
			b := shift(b, -1);
		}
		u;
	}
}

extend Byte:Join(OutputType, InputType) == add {
	import from Z;
	(p:TextWriter) << (b:%):TextWriter	== p << b::Z;
	<< (p:TextReader):%			== lowByte((<< p)@Z);
}
