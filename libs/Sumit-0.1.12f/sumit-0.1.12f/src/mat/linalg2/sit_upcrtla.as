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
---------------------------- sit_upcrtla.as ---------------------------------
-- Copyright (c) Helene Prieto 2000
-- Copyright (c) INRIA 2000, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 2000, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"


macro {
	I==MachineInteger;
	Z==Integer;
	A==PrimitiveArray;
}

#if ALDOC
\thistype{UnivariatePolynomialCRTLinearAlgebra}
\History{Helene Prieto}{July 2000}{created}
\Usage{import from \this(R, RX, M)}
\Params{
{\em R} & \astype{CommutativeRing} & The coefficient ring\\
{\em RX} & \astype{UnivariatePolynomialCategory} R & Polynomials over $R$\\
{\em M} & \astype{MatrixCategory} RX & A matrix type over $RX$\\
}
\Descr{\this(F, FX, M) provides basic linear algebra functionalities
using the Chinese Remainder Theorem from $RX$ to $R$ for matrices over $RX$.}
\begin{exports}
\asexp{degreeBound}:
& M $\to$ \astype{Integer}) & Degree bound for the determinant\\
\asexp{determinant}: & M $\to$ RX & Determinant\\
                     & (M, RX) $\to$ RX & \\
                     & (M, RX, \astype{Integer}) $\to$ RX & \\
\end{exports}
#endif

UnivariatePolynomialCRTLinearAlgebra(F:CommutativeRing,
	UPF:UnivariatePolynomialCategory F,
	M:MatrixCategory UPF): with {
		degreeBound: M -> Z;
#if ALDOC
\aspage{degreeBound}
\Usage{\name~a}
\Signature{M}{\astype{Integer}}
\Params{ {\em a} & M & A matrix\\ }
\Retval{Returns $n$ such that $\deg |a| \le n$.}
#endif
		determinant: M -> Partial UPF;
		determinant: (M, UPF) -> Partial UPF;
		determinant: (M, UPF, Z) -> Partial UPF;
#if ALDOC
\aspage{determinant}
\Usage{\name~a\\ \name(a, d)\\ \name(a, d, n)}
\Signatures{
\name: & M $\to$ RX\\
\name: & (M, RX) $\to$ RX\\
\name: & (M, RX, \astype{Integer}) $\to$ RX\\
}
\Params{
{\em a} & M & A matrix\\
{\em d} & RX & A known factor of $|a|$ (optional)\\
{\em n} & \astype{Integer} & A known degree bound on $|a|$ (optional)\\
}
\Retval{All calls to \name return the determinant of $a$.}
\Remarks{ The extra parameters $d$ and $n$ are optional. If they are provided,
then $d$ must divide $|a|$ exactly, and $n$ must be such that
$\deg |a| \le n$. }
#endif
} == add {
	local fin?:Boolean == F has FiniteSet;

	determinant(m:M):Partial UPF == determinant(m, 1$UPF, degreeBound m);
	determinant(m:M, d:UPF):Partial UPF == determinant(m, d, degreeBound m);

	if F has FiniteSet then {
		-- fd = garanteed factor of det(m);
		-- B is such that deg(det(m)) <= B)
		determinant(m:M, fd:UPF, B:Z): Partial UPF == {
			import from Boolean;
			assert(~zero? fd);
			B := B - degree fd;
			B >= #$F => failed;
			[deter(m, fd, B)];
		}
	}
	else {
		-- fd = garanteed factor of det(m);
		-- B is such that deg(det(m)) <= B)
		determinant(m:M,fd:UPF,B:Z): Partial UPF == {
			import from Boolean;
			assert(~zero? fd);
			[deter(m, fd, B - degree fd)];
		}
	}

	-- fd = garanteed factor of det(m);
	-- B is such that deg(det(m)/fd) <= B)
	local deter(m:M, fd:UPF, B:Z): UPF == {
		import from F, I, A F, A A F, Generator F, A Generator F;
		import from LinearAlgebra(F,DenseMatrix F), Boolean, Partial F;

		assert(~zero? fd); assert(B >= 0);
		n := numberOfRows m;
		assert(n > 0); assert(n=numberOfColumns m);
		mp: DenseMatrix F := zero(n,n);
		mg: A A Generator F := new n;

		i:I := 0; while i<n repeat {
			mg.i := new n;
			j:I:=0; while j<n repeat {
				mg.i.j:=values(m(i+1,j+1),0);
				j:=next j;
			}
			i:= next i;
		}

		N: UPF :=1;
		det: UPF :=0;
		firststep:=true;

		k:Z :=0;
		x := monom;
	
		while k <= B repeat {
			xk := k::F;
			p:UPF := x - xk::UPF;
			fdmod := fd xk;
			if ~zero? fdmod then {	-- must compute det mod x-k
				i:=0; while i<n repeat {
					j:=0; while j<n repeat { 
						mp(i+1,j+1):=next! mg.i.j;
						j := next j;
					}
					i := next i;
				}
				d := determinant mp;
				assert(~failed? exactQuotient(d, fdmod));
				d := quotient(d, fdmod);
				if firststep then det := d::UPF;
				else {	-- combine d/fdmod with previous values
					b := d - det(xk);
					assert(~failed? exactQuotient(b,N(xk)));
					b := quotient(b, N(xk));
					det := add!(det, b * N);
				}
			}
			firststep := false;
			N := times!(N, p);
			k := next k;
		}
		times!(det, fd);
	}

	degreeBound(m:M):Z == {
		import from UPF,I;
		b:Z := 0;
		(r, c) := dimensions m;
		for i in 1..r repeat {
			d:Z := 0;
			for j in 1..c | ~zero?(p := m(i, j)) repeat {
				dg := degree p;
				if dg > d then d := dg;
			}
			b:=b+d;
		}
		bcol := b;
		b := 0;
		for j in 1..c repeat {
			d:Z := 0;
			for i in 1..r | ~zero?(p := m(i, j)) repeat {
				dg := degree p;
				if dg > d then d := dg;
			}
			b:=b+d;
		}
		min(b, bcol);
	}
}

