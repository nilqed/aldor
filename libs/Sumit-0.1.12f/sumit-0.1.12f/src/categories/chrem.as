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
-------------------------------- chrem.as ------------------------------------
#include "sumit"

macro SI == SingleInteger;

#if ASDOC
\thistype{ChineseRemaindering}
\History{Laurent Bernardin}{17/8/95}{created}
\History{Manuel Bronstein}{19/4/96}{
Curried up combine function for caching the modular inversion.
Added special signature for bigint/machine-int moduli pairs.}
\Usage{import from \this R}
\Params{
{\em R} & SumitEuclideanDomain & an Euclidean Domain.\\
}
\Descr{\this~provided Garner's Chinese Remaindering Algorithm for
an arbitrary Euclidean Domain.}
\begin{exports}
combine: & (R,R) $\to$ (R,R) $\to$ R &
combine interpolated result with one more modulus.\\
interpolate: & (List R,List R) $\to$ R &
interpolate given residues and moduli.\\
\end{exports}
\begin{exports}[if R has IntegerCategory then]
combine: & (R,SingleInteger) $\to$ (R,SingleInteger) $\to$ R &
combine with one more modulus.\\
\end{exports}
#endif

ChineseRemaindering(R:SumitEuclideanDomain): with {
	combine:	(R,R) -> (R,R) -> R;
	if R has IntegerCategory then {
		combine: (R, SI) -> (R, SI) -> R;
	}
#if ASDOC
\aspage{combine}
\Usage{\name(M,m)\\ \name(M,m)(A,a)}
\Signatures{
\name: & (R,R) $\to$ (R,R) $\to$ R\\
\name: & (R,SingleInteger) $\to$ (R,SingleInteger) $\to$ R\\
}
\Params{
{\em M} & R & A product of primes.\\
{\em m} & R or SingleInteger & A new modulus.\\
{\em A} & R & The interpolated value modulo {\em M}.\\
{\em a} & R or SingleInteger & The residue modulo {\em m}.\\
}
\Retval{
Returns the unique $X$ in $R/(mM)$ such that
$X = A \pmod M$ and $X = a \pmod m$.
}
#endif
	interpolate:	(List R,List R)	->	R;
#if ASDOC
\aspage{interpolate}
\Usage{\name(p,m)}
\Signature{(List R,List R)}{R}
\Params{ {\em p} & List R & A list of residues.\\
	 {\em m} & List R & A list of moduli.}
\Retval{Returns the interpolated value from the residues and the corresponding moduli.}
#endif

} == add {
	local mustBalance?:Boolean == R has IntegerCategory;

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
			ASSERT(M > 0); ASSERT(m > 0); ASSERT(odd? m);
			mz := m::R;
			mover2 := shift(m, -1);
			s := mod_/(1, retract integer(M rem mz), m);
			(A:R, a:SI):R +-> {
				aa := retract integer(A rem mz);
				-- all args to mod_X must be positive!
				if a < 0 then a := a + m;
				aminusA := {
					aa < 0 => mod_+(a, -aa, m);
					mod_-(a, aa, m);
				}
				b := mod_*(s, aminusA, m);
				-- balance out result
				if b > mover2 then b := b - m;
				A + (b::R) * M;
			}
		}
	}

	interpolate(p:List R, m:List R):R == {
		import from SI;
		ASSERT(#p=#m);
		ASSERT(#p>0);
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
	P == DenseUnivariatePolynomial(F,"x");
}

inttest():Boolean == {
	import from Z,List Z,ChineseRemaindering Z;

	a := interpolate([4551,4671],[7927,7919]);
	a = 123456 => true;
	false;
}

polytest():Boolean == {
	import from SingleInteger,Integer,P,ChineseRemaindering P,List P;

	getx():P == { import from F; monomial(1,1); }
	x := getx();

	a := interpolate([6*1,0,7*1],[x-1,x-2*1,x-3*1]);
	a = x^2+2*x+3*1 => true;
	false;
}

print << "Testing ChineseRemaindering..." << newline;
sumitTest("for integers",inttest);
sumitTest("for polynomials",polytest);
print << newline;
#endif
