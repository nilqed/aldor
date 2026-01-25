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
----------------------------- sit_duts.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I == MachineInteger;
	Z == Integer;
	TREE == ExpressionTree;
	SEQ == Sequence;
}

#if ALDOC
\thistype{DenseUnivariateTaylorSeries}
\History{Manuel Bronstein}{30/5/2000}{created}
\Usage{ import from \this~R\\ import from \this(R, x) }
\Params{
{\em R} & \astype{SumitType} & The coefficient domain\\
        & \astype{ArithmeticType} &\\
{\em x} & \astype{Symbol} & The variable name (optional)\\
}
\Descr{\this(R, x) implements univariate Taylor series with coefficients
in R.}
\begin{exports}
\category{\astype{UnivariateTaylorSeriesCategory} R}\\
\end{exports}
#endif

DenseUnivariateTaylorSeries(R:Join(ArithmeticType, SumitType),
	avar:Symbol == new()): UnivariateTaylorSeriesCategory R == SEQ R add {
	Rep == SEQ R;
	import from Rep;

	local seq(s:%):SEQ R	== rep s;
	finite?(s:%):Boolean	== finite? seq s;
	series(s:SEQ R):%	== per s;
	extree(s:%):TREE	== s extree avar;
	local dummy:Symbol	== { import from String; -"dummy"; }
	(p:TextWriter) << (s:%):TextWriter == p(s, avar);

	apply(s:%, x:TREE):TREE == {
		import from Boolean, I, Z, R, List TREE;
		import from UnivariateMonomial(R, dummy);
		zero? s => extree(0@R);
		l:List(TREE) := empty;
		n := #(rs := seq s);
		for i in 0..prev n | ~zero?(c := rs.i) repeat {
			m := monomial(c, i::Z)@UnivariateMonomial(R, dummy);
			l := cons(m x, l);
		}
		if (b := bound rs) < 0 or n < b then {
			m := monomial(1, n::Z)@UnivariateMonomial(R, dummy);
			l := cons(ExpressionTreeBigO [m x], l);
		}
		empty? l => extree(0@R);
		empty? rest l => first l;
		ExpressionTreePlus reverse! l;
	}

	degree(s:%):Partial Z == {
		import from I, Z;
		(n := bound seq s) < 0 => failed;
		[prev(n)::Z];
	}

	if R has CommutativeRing then {
		if R has QRing then {
			integrate(s:%, k:Z):% == {
				import from I, R, Stream R;
				n := machine k;
				assert(n >= 0);
				zero? n => s;
				rs := seq s;
				(cs := bound rs) < 0 =>
					series sequence stream(0, int(rs, n));
				series sequence stream(0, int(rs, n), cs+n, 0);
			}

			local int(s:SEQ R, n:I)(k:I):R == {
				import from Z;
				(m := k - n) < 0 => 0;
				inv(factorial(k::Z, -1, n)) * s.m;
			}
		}

		differentiate(s:%, k:Z):% == {
			import from I, R, Stream R;
			n := machine k;
			assert(n >= 0);
			zero? n => s;
			rs := seq s;
			(cs := bound rs) < 0 =>
				series sequence stream(0, diff(rs, n));
			(e := cs - n) <= 0 => 0;
			series sequence stream(0, diff(rs, n), e, 0);
		}

		local diff(s:SEQ R, n:I)(k:I):R == {
			import from Z;
			m := k + n;
			factorial(m::Z, 1, n) * s.m;
		}
	}

	(s:%) * (t:%):% == {
		import from I, R, Stream R;
		zero? s or zero? t => 0;
		cs := bound(rs := seq s);
		ct := bound(rt := seq t);
		cs < 0 or ct < 0 => series sequence stream(0, naive(rs, rt));
		assert(cs > 0); assert(ct > 0);
		series sequence stream(0, naive(rs, rt), prev(cs + ct), 0);
	}

	local naive(s:SEQ R, t:SEQ R): I -> R == {
		(m:I):R +-> {
			r:R := 0;
			for i in 0..m repeat r := add!(r, s.i * t(m-i));
			r;
		}
	}
}

