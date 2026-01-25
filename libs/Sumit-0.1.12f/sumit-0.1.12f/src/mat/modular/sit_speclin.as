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
----------------------------   sit_speclin.as   -----------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it ©INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	B == Boolean;
	I == MachineInteger;
	A == PrimitiveArray;
}

#if ALDOC
\thistype{SpecializationLinearAlgebra}
\History{Manuel Bronstein}{4/10/2000}{created}
\Usage{import from \this(R, M)}
\Params{
{\em R} & \astype{CommutativeRing} & The coefficient domain\\
        & \astype{Specializable} & \\
{\em M} & \astype{MatrixCategory} R & A matrix type\\
}
\Descr{\this(R, M) provides basic linear algebra functionalities
using specializations for matrices over $R$.}
\begin{exports}
\asexp{rankLowerBound}:
& M $\to$ \astype{Partial} \builtin{Cross}
(\astype{Boolean}, \astype{MachineInteger}) &
Probable rank\\
\end{exports}
#endif

SpecializationLinearAlgebra(R:Join(CommutativeRing, Specializable),
				M:MatrixCategory R): with {
	rankLowerBound: M -> Partial Cross(B, I);
#if ALDOC
\aspage{rankLowerBound}
\Usage{\name~a}
\Signature{M}
{\astype{Partial} \builtin{Cross}(\astype{Boolean}, \astype{MachineInteger})}
\Params{ {\em a} & M & A matrix\\ }
\Retval{ Returns \failed if specialization failed,
otherwise $(rank?, r)$ such that $r \le \mbox{rank}(a)$,
and $r$ is exactly the rank of $a$ if $rank?$ is \true. }
\Remarks{$r$ can also happen to be the rank of $a$ when $rank?$ is \false,
but the algorithm was unable to prove it.}
#endif
} == add {
	rankLowerBound(m:M):Partial Cross(B, I) == {
		import from Boolean, I, A I, A A I, LazyHalfWordSizePrimes;
		(r, c) := dimensions m;
		mp:A A I := new r;
		for i in 0..prev r repeat mp.i := new c;
		for i in 1..2 repeat {
			p := randomPrime();
			~failed?(u := rankLowerBound(m, mp, p)) => return u;
		}
		failed;
	}

	local rankLowerBound(m:M, mp:A A I, p:I):Partial Cross(B, I) == {
		import from I, ModulopGaussElimination;
		(r, c) := dimensions m;
		maxrank := min(r, c);
		for i in 1..2 repeat {
			specialize!(mp, m, p) => {
				rk := rank!(mp, r, c, p);
				return [(rk = maxrank, rk)];
			}
		}
		failed;
	}

	local specialize!(mp:A A I, m:M, p:I):Boolean == {
		macro F == SmallPrimeField0 p;
		import from I, A I, A A I, F, Partial F, PartialFunction(R, F);
		(r, c) := dimensions m;
		sigma := partialMapping(specialization(F)$R);
		for i in 1..r repeat {
			rowi := mp(prev i);
			for j in 1..c repeat {
				failed?(u := sigma m(i, j)) => return false;
				rowi(prev j) := machine retract u;
			}
		}
		true;
	}
}
