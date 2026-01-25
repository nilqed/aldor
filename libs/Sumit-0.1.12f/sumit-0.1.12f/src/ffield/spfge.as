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
------------------------------ spgge.as ------------------------------------
#include "sumit"

#if ASDOC
\thistype{SmallPrimeFieldGaussElimination}
\History{Thom Mulders}{8 July 96}{created OGE for general fields}
\History{Manuel Bronstein}{15 December 98}{adapted for small prime fields}
\Usage{import from \this(F, M)}
\Params{
{\em F} & SmallPrimeFieldCategory0 & A coefficient field\\
{\em M} & MatrixCategory0 F& A matrix type over F\\
}
\begin{exports}
\category{EliminationCategory(F, M)}\\
\end{exports}
\Descr{
This domain implements ordinary Gaussian elimination on matrices
over small prime fields.
}
#endif

macro {
	SI == SingleInteger;
	ARR == PrimitiveArray SI;
	Mp == PrimitiveArray ARR;
	V == Vector F;
}

-- Do not use the log table for small prime, since the lazy strategy is better
SmallPrimeFieldGaussElimination(F:SmallPrimeFieldCategory0,M:MatrixCategory0 F):
	EliminationCategory(F, M) == add {

	import from ModulopGaussElimination;

	local charac:SI	== { import from Integer; retract(characteristic$F); }
	local reduce(b:Mp, r:SI, c:SI):M == reduce!(zero(r, c), b, r, c);
	denominators(a:M, p:ARR, r:SI, st:ARR):PrimitiveArray F	== new(r, 1);

	rowEchelon!(a:M):(ARR, SI, ARR, SI) == {
		TRACE("SmallPrimeFieldGaussElimination::rowEchelon!: a = ", a);
		(ra, ca) := dimensions a;
		res := rowEchelon!(m := lift a, ra, ca, charac);
		reduce!(a, m, ra, ca);	-- transfer the side-effect to a
		res;
	}

	extendedRowEchelon!(a:M):(ARR, SI, ARR, SI, M) == {
		(ra, ca) := dimensions a;
		(p, r, st, d, b) :=
			extendedRowEchelon!(m := lift a, ra, ca, charac);
		reduce!(a, m, ra, ca);	-- transfer the side-effect to a
		(p, r, st, d, reduce(b, ra, ra));
	}

	deter(a:M, p:ARR, r:SI, st:ARR, d:SI):F ==
		deter(lift a, rows a, cols a, p, r, st, d, charac) :: F;

	dependence(gen:Generator V, n:SI):(M, ARR, SI, F) == {
		(b, a, r, m) := dependence(lift(gen, n), n, charac);
		(reduce(b, n, r), a, r, m::F);
	}

	local lift(g:Generator V, n:SI):Generator ARR == generate {
		a:ARR := new(n, 0);
		for v in g repeat yield lift!(a, v, n);
	}

	local lift!(a:ARR, v:V, n:SI):ARR == {
		import from F;
		assert(n = #v);
		for i in 1..n repeat a.i := lift(v.i);
		a;
	}

	local lift(a:M):Mp == {
		import from F;
		(r, c) := dimensions a;
		b:Mp := new r;
		for i in 1..r repeat {
			b.i := new c;
			for j in 1..c repeat b.i.j := lift a(i, j);
		}
		b;
	}

	-- copies b into a
	local reduce!(a:M, b:Mp, r:SI, c:SI):M == {
		import from F;
		for i in 1..r repeat for j in 1..c repeat a(i, j) := (b.i.j)::F;
		a;
	}
}
