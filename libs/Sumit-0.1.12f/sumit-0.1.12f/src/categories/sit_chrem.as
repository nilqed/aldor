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
----------------------------- sit_chrem.as ------------------------------------
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"

macro SI == MachineInteger;

#if ALDOC
\thistype{ChineseRemaindering}
\History{Laurent Bernardin}{17/8/95}{created}
\History{Manuel Bronstein}{19/4/96}{
Curried up combine function for caching the modular inversion.
Added special signature for bigint/machine-int moduli pairs.}
\Usage{import from \this R}
\Params{
{\em R} & \astype{EuclideanDomain} & an Euclidean Domain.\\
}
\Descr{\this~provided Garner's Chinese Remaindering Algorithm for
an arbitrary Euclidean Domain.}
\begin{exports}
\asexp{combine}: & (R,R) $\to$ (R,R) $\to$ R &
combine interpolated result with new modulus.\\
\asexp{interpolate}: & (\astype{List} R,\astype{List} R) $\to$ R &
interpolate given residues and moduli.\\
\end{exports}
\begin{exports}[if R has \astype{IntegerCategory} then]
\asexp{combine}:
& (R,\astype{MachineInteger}) $\to$ (R,\astype{MachineInteger}) $\to$ R &
combine with new modulus.\\
\end{exports}
#endif

ChineseRemaindering(R:EuclideanDomain): with {
	combine:	(R,R) -> (R,R) -> R;
	if R has IntegerCategory then {
		combine: (R, SI) -> (R, SI) -> R;
	}
#if ALDOC
\aspage{combine}
\Usage{\name(M,m)\\ \name(M,m)(A,a)}
\Signatures{
\name: & (R,R) $\to$ (R,R) $\to$ R\\
\name: & (R,\astype{MachineInteger}) $\to$ (R,\astype{MachineInteger}) $\to$ R\\
}
\Params{
{\em M} & R & A product of primes.\\
{\em m} & R & A new modulus.\\
        & \astype{MachineInteger} & \\
{\em A} & R & The interpolated value modulo {\em M}.\\
{\em a} & R & The residue modulo {\em m}.\\
        & \astype{MachineInteger} & \\
}
\Retval{
Returns the unique $X$ in $R/(mM)$ such that
$X = A \pmod M$ and $X = a \pmod m$.
}
#endif
	interpolate:	(List R,List R)	->	R;
#if ALDOC
\aspage{interpolate}
\Usage{\name(p,m)}
\Signature{(\astype{List} R,\astype{List} R)}{R}
\Params{ {\em p} & \astype{List} R & A list of residues.\\
	 {\em m} & \astype{List} R & A list of moduli.}
\Retval{Returns the interpolated value from the residues and the
corresponding moduli.}
#endif
} == add {
	local mustBalance?:Boolean	== R has IntegerCategory;
	local maxhalf:SI		== shift(1, prev(4 * bytes$SI));

	combine(M:R, m:R):(R,R) -> R == {
		import from Integer, Partial R;
		TRACE("computing inverse of ", M rem m);
		TRACE("modulo ",m);
		s := retract diophantine(M rem m, 1, m);
		mover2:R := { mustBalance? => m quo (2::R); 0 };
		TRACE("result=",s);
		(A:R, a:R):R +-> {
			b := (s * (a - (A rem m))) rem m;
			-- the following is only for integer-like rings
			if mustBalance? and greater?(b, mover2) then b := b - m;
			A + b * M;
		}
	}

	if R has IntegerCategory then {
		local greater?(a:R, b:R):Boolean == a > b;

		combine(M:R, m:SI):(R,SI) -> R == {
			import from Integer;
			assert(M > 0); assert(m > 0); assert(odd? m);
			mover2 := shift(m, -1);
			s := modInverse(M mod m, m);
			m > maxhalf => {
				(A:R, a:SI):R +-> {
					-- all args to mod_X must be positive!
					if a < 0 then a := a + m;
					aminusA := mod_-(a, A mod m, m);
					b := mod_*(s, aminusA, m);
					-- balance out result
					if b > mover2 then b := b - m;
					A + (b::R) * M;
				}
			}
			(A:R, a:SI):R +-> {
				-- all args to mod_X must be positive!
				if a < 0 then a := a + m;
				aminusA := mod_-(a, A mod m, m);
				b := (s * aminusA) rem m;
				-- balance out result
				if b > mover2 then b := b - m;
				A + (b::R) * M;
			}
		}
	}

	interpolate(p:List R, m:List R):R == {
		import from SI;
		assert(#p=#m);
		assert(#p>0);
		a := first p; p := rest p;
		M := first m; m := rest m;
		while ~empty? p repeat {
			np := first p; p := rest p;
			nm := first m; m := rest m;
			a  := combine(M, nm)(a, np);
			M  := nm * M;
		}
		a;
	}
}

#if SUMITTEST
------------------ test chrem.as -----------------
#include "sumittest"

macro {
	Z == Integer;
	F == SmallPrimeField 11;
	P == DenseUnivariatePolynomial F;
}

local inttest():Boolean == {
	import from Z,List Z,ChineseRemaindering Z;

	a := interpolate([4551,4671],[7927,7919]);
	a = 123456 => true;
	false;
}

local polytest():Boolean == {
	import from MachineInteger,Integer,P,ChineseRemaindering P,List P;

	x := monom;
	a := interpolate([6*1,0,7*1],[x-1,x-2*1,x-3*1]);
	a = x^2+2*x+3*1 => true;
	false;
}

stdout << "Testing sit_chrem..." << endnl;
sumitTest("CRT for integers",inttest);
sumitTest("CRT for polynomials",polytest);
stdout << endnl;
#endif
