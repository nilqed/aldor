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
------------------------------ sit_vector.as ------------------------------
-- Copyright (c) Marco Codutti 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995
-----------------------------------------------------------------------------

#include "sumit"

macro {
	ARR == Array;
	PA  == PrimitiveArray;
	I  == MachineInteger;
}

#if ALDOC
\thistype{Vector}
\History {Marco Codutti}{10 May 1995}{created.}
\History {Manuel Bronstein}{30/11/1999}{redesigned using Array}
\Usage   {import from \this~R}
\Params{
{\em R} & \astype{SumitType} & The coefficient domain\\
        & \astype{AdditiveType} &\\
}
\Descr   {\this~R provides vectors of arbitrary size with entries in R.
They are 1--indexed and without bound checking.}
\begin{exports}
\category{\astype{AdditiveType}}\\
\category{\astype{BoundedFiniteLinearStructureType} R}\\
\category{\astype{SumitType}}\\
\asexp{zero}: & \astype{MachineInteger} $\to$ \% & zero vector\\
\asexp{zero!}: & \% $\to$ () & make all the entries zero\\
\asexp{zero?}: & \% $\to$ \astype{Boolean} & test if all entries are zero\\
\end{exports}
\begin{exports}[if R has \astype{ArithmeticType} then]
\category{\astype{LinearCombinationType} R}\\
\asexp{dot}: & (\%, \%) $\to$ R & dot product\\
\asexp{tensor}: & (\%, \%) $\to$ \% & tensor product\\
\end{exports}
\begin{exports}[if R has \astype{Ring} then]
\asexp{random}: & () $\to$ \% & random vector\\
 & \astype{MachineInteger} $\to$ \% & \\
\end{exports}
#endif

Vector(R:Join(AdditiveType, SumitType)):
	Join(AdditiveType, BoundedFiniteLinearStructureType R, SumitType) with {
		if R has ArithmeticType then {
			LinearCombinationType R;
			dot: (%, %) -> R;
#if ALDOC
\aspage{dot}
\Usage{\name(u,v)}
\Signature{(\%,\%)}{R}
\Params{{\em u, v} & \% & Vectors of the same size\\ }
\Retval{Returns $u \cdot v = \sum_i u_i v_i$.}
#endif
		}
		if R has Ring then {
			random:        ()        -> %;
			random:        I        -> %;
#if ALDOC
\aspage    {random}
\Usage     {\name()\\ \name~n}
\Signatures{
\name: & () $\to$ \%\\
\name: & \astype{MachineInteger} $\to$ \%\\
}
\Params  {{\em n} & \astype{MachineInteger} & The dimension of the new vector.}
\Retval    {\name() returns a random vector of size at most 100, while
\name(n) returns a random vector of size n.}
#endif
		}
		if R has ArithmeticType then {
			tensor:	(%, %) -> %;
#if ALDOC
\aspage{tensor}
\Usage{\name(u,v)}
\Signature{(\%,\%)}{\%}
\Params{{\em u}, {\em v} & \% & Vectors with coefficients from R.}
\Retval{Returns
$u \otimes v = (u_1 v_1, u_1 v_2, \dots, u_1 v_m, u_2 v_1, \dots, u_n v_m)$.}
#endif
		}
		zero:		I	-> %;
		zero!:		%	-> ();
		zero?:		%	-> Boolean;
#if ALDOC
\aspage{zero}
\astarget{\name!}
\astarget{\name?}
\Usage     {\name~n\\ \name!~v\\ \name?~v}
\Signatures{
\name:  & \astype{MachineInteger}) $\to$ \%\\
\name!: & \% $\to$ ()\\
\name?: & \% $\to$ \astype{Boolean}\\
}
\Params{
{\em n} & \astype{MachineInteger} & The dimension of the new vector\\
{\em v} & \% & A vector with coefficients from R\\
}
\Descr{\name(n) returns a zero vector of size $n$, while
\name!(v) fills $v$ with $0$'s and \name?(v)
returns \true if all the entries of {\em v} are $0$, \false otherwise.}
#endif
} == ARR R add {
	Rep == ARR R;

	0:%			== empty;
	zero(n:I):%		== { import from R; new(n, 0); }
	add!(u:%, v:%):%	== zip!(+$R, u, v);
	minus!(u:%, v:%):%	== zip!(-$R, u, v);
	(u:%) + (v:%):%		== zip(+$R, u, v);
	(u:%) - (v:%):%		== zip(-$R, u, v);
	minus!:% -> %		== map!(-$R);
	-:% -> %		== map(-$R);

	zero?(u:%):Boolean == {
		import from R;
		for x in u repeat { ~zero?(x) => return false; }
		true;
	}

	-- Vector's are 1-indexed while Array's are 0-indexed
	apply(u:%, n:I):R == {
		import from Rep, PA R;
		assert(n > 0); assert(n <= #u);
		data(rep u)(prev n);
	}

	-- Vector's are 1-indexed while Array's are 0-indexed
	set!(u:%, n:I, r:R):R == {
		import from Rep, PA R;
		assert(n > 0); assert(n <= #u);
		data(rep u)(prev n) := r;
	}

	-- Vector's are 1-indexed while Array's are 0-indexed
	zero!(u:%):() == {
		import from Rep, I, R, PA R;
		n := #u;
		assert(n >= 0);
		a := data rep u;
		for i in 0..prev n repeat a.i := 0;
	}

	-- Vector's are 1-indexed while Array's are 0-indexed
	find(r:R, u:%):(%, I) == {
		(w, pos) := find(r, rep u)$Rep;		-- not a recursive call!
		empty? per w => (per w, pos);
		(per w, next pos);
	}

	zip(f:(R, R) -> R, u:%, v:%) : % == {
		import from I, Rep, PA R, R;
		assert(#u=#v);
		pu := data rep u; pv := data rep v;
		p:PA R := new(n := #v);
		for i in 0..prev n repeat p.i := f(pu.i, pv.i);
		per array(p, n);
	}

	zip!(f:(R, R) -> R, u:%, v:%) : % == {
		import from I, Rep, PA R, R;
		assert(#u=#v);
		pu := data rep u; pv := data rep v;
		for i in 0..prev(#v) repeat pu.i := f(pu.i, pv.i);
		u;
	}

	extree (v:%) : ExpressionTree == {
		import from List ExpressionTree, R;
		ExpressionTreeVector [extree x for x in v];
	}

	if R has ArithmeticType then {
		add!(v:%, r:R, w:%):% == zip!((x:R, y:R):R +-> x + r * y, v, w);

		(r:R) * (v:%):% == {
			zero? r => zero(#v);
			one? r => v;
			r = -1 => -v;
			map((x:R):R +-> r * x)(v);
		}

		dot(u:%, v:%):R == {
			import from I, R;
			assert(#u=#v);
			d:R := 0;
			for x in u for y in v repeat d := d + x * y;
			d;
		}

		tensor(u:%, v:%):% == {
			import from I, R, Rep;
			w := per new(#u * #v);
			k:I := 1;	-- Vector's are 1-indexed
			for x in u repeat for y in v repeat {
				w.k := x * y;
				k := next k;
			}
			w;
		}

		times! (r:R, v:%) : % == {
			zero? r => map!((x:R):R +-> 0)(v);
			one? r => v;
			r = -1 => minus! v;
			map!((x:R):R +-> r * x)(v);
		}
	}

	if R has Ring then {
		random():% == { import from I; random(1+random()$I mod 100); }

		random (n:I) : % == {
			import from R;
			assert(n >= 0);
			u := zero n;
			for i in 1..n repeat u.i := random();
			u;
		}
	}
}

#if SUMITTEST
---------------------- test sit__vector.as --------------------------
#include "sumittest"

local inplace():Boolean == {
	macro R == Integer;
	macro V == Vector R;
	import from R,V,List R;

	u:V := [1,2,3,4,5,6];
	v:V := [6,5,4,3,2,1];
	w:V := [1,1,1,1,1,1];
	t := copy u;

	w := times!(7,w);
	u := add!(u,v);
	u ~= w => false;
	u := minus!(u,v);
	u ~= t => false;
	zero? add!( t, minus! u );
}

stdout << "Testing sit__vector..." << endnl;
sumitTest("in-place operations", inplace);
stdout << endnl;
#endif
