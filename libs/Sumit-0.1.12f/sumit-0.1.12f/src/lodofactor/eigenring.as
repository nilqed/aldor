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
------------------------- eigenring.as --------------------------
#include "sumit"

#if ASDOC
\thistype{Eigenring}
\History{Manuel Bronstein}{30/6/97}{created}
\Usage{import from \this(R, RX, RXD, RxD);}
\Params{
{\em R} & GcdDomain        & Coefficients of the polynomials\\
        & RationalRootRing & \\
{\em RX} & UnivariatePolynomialCategory R &
Coefficients of the differential operators\\
{\em RXD} & LODO RX & Differential operators\\
{\em RxD} & LODO Quotient RX & Differential operators\\
}
\begin{aswhere}
LODO &==& LinearOrdinaryDifferentialOperatorCategory\\
\end{aswhere}
\Descr{\this(R, RX, RXD, RxD) provides an eigenring-based factoriser
for completely reducible linear ordinary differential operators with
coefficients in $R[x]$ or $R(x)$.}
\begin{exports}
eigenring & RXD $\to$ Vector RxD & Eigenring\\
eigenring & RxD $\to$ Vector RxD & Eigenring\\
\end{exports}
#endif

macro {
	Z	== Integer;
	RF	== Quotient Rx;
	V	== Vector;
}

Eigenring(R: Join(GcdDomain, RationalRootRing),
	Rx: UnivariatePolynomialCategory R,
	RxD: LinearOrdinaryDifferentialOperatorCategory Rx,
	RFD: LinearOrdinaryDifferentialOperatorCategory RF): with {
		eigenring: RxD -> V RFD;
		eigenring: RFD -> V RFD;
#if ASDOC
\aspage{eigenring}
\Usage{\name~L}
\Signatures{
\name: & RXD $\to$ Vector RxD\\
\name: & RxD $\to$ Vector RxD\\
}
\Params{
{\em L} & RXD & A differential operator\\
        & RxD &\\
}
\Retval{Returns a basis for the space
$$
{\cal E}_{{\cal D}}(L) = \{ R \mbox{ mod } L \st L R = Q L \mbox{ for some } Q\}
$$
}
\Remarks{The current implementation uses the cyclic vector method.}
\seealso{endomorphisms(LODSRationalSolutions)}
#endif
} == add {
	eigenring(L:RxD):V RFD == {
		import from LODSRationalSolutions(R, Rx),
			LinearOrdinaryDifferentialSystem Rx,
			System2LinearOrdinaryDifferentialOperator(Rx, RxD);
		operator(rationalKernel eigenTensor companionSystem L,degree L);
	}

	eigenring(L:RFD):V RFD == {
		import from LODSRationalSolutions(R, Rx),
			LinearOrdinaryDifferentialSystem RF,
			System2LinearOrdinaryDifferentialOperator(RF, RFD);
		operator(rationalKernel eigenTensor companionSystem L,degree L);
	}

	-- take the 1st row of each matrix of the endomorphisms ring,
	-- i.e. entries 1, n+1, 2n+1,... of the solutions of the tensor
	local operator(mat:DenseMatrix RF, m:Z):V RFD == {
		import from SingleInteger, RF, RFD;
		n:SingleInteger := retract m;
		ASSERT(#v = n * n);
		v:V RFD := zero(c := cols mat);
		for i in 1..c repeat {
			v.i := 0;
			for j in prev n..0 by -1 repeat
				v.i := add!(v.i, mat(next(j * n), i), j::Z);
		}
		v;
	}
}

#if SUMITTEST
---------------------- test eigenring.as --------------------------
#include "sumittest"

macro {
	Z == Integer;
	ZX == DenseUnivariatePolynomial(Z, "x");
	Zx == Quotient ZX;
	ZXD == LinearOrdinaryDifferentialOperator(ZX, "D");
	ZxD == LinearOrdinaryDifferentialOperator(Zx, "D");
}

local zeigen():Boolean == {
	import from SingleInteger, Z, ZX, Zx, ZXD, ZxD, Vector ZxD;
	import from Eigenring(Z, ZX, ZXD, ZxD);
	x:ZX := monom;
	D:ZXD := monom;
	L := 16*x^2*D^2 + (3@Z)::ZXD;
	LL := (16*x^2)::Zx * (monom$ZxD)^2 + (3@Z)::ZxD;
	E := eigenring L;
	#E ~= 2 => false;
	for i in 1..#E repeat
		~zero?(rightRemainder(LL * E.i, LL)) => return false;
	true;
}

local qeigen():Boolean == {
	import from SingleInteger, Z, ZX, Zx, ZxD, Vector ZxD;
	import from Eigenring(Z, ZX, ZXD, ZxD);
	x:ZX := monom;
	D:ZxD := monom;
	L := (16*x^2)::Zx * D^2 + (3@Z)::ZxD;
	E := eigenring L;
	#E ~= 2 => false;
	for i in 1..#E repeat
		~zero?(rightRemainder(L * E.i, L)) => return false;
	true;
}

print << "Testing eigenrings..." << newline;
sumitTest("2nd order over polynomials", zeigen);
sumitTest("2nd order over fractions", qeigen);
print << newline;
#endif
