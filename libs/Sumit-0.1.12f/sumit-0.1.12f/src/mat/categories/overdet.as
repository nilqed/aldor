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
------------------------- overdet.as --------------------------
#include "sumit"

#if ASDOC
\thistype{OverdeterminedSystemSolver}
\History{Manuel Bronstein}{8/6/98}{created}
\Usage{import from \this(R, M)}
\Params{
{\em R} & IntegralDomain & A domain\\
{\em M} & MatrixCategory0 R & A matrix type over R\\
}
\Descr{\this(R, M) provides a solver for overdetermined linear algebraic
equations with coefficients in R.}
\begin{exports}
nullSpace! & (M, M $\to$ List Vector R) $\to$ List Vector R\\
& Solve an overdetermined system\\
\end{exports}
#endif

macro {
	I	== SingleInteger;
	V	== Vector;
}

OverdeterminedSystemSolver(R:IntegralDomain, M: MatrixCategory0 R): with {
		nullSpace!: (M, M -> List V R) -> List V R;
#if ASDOC
\aspage{nullSpace!}
\Usage{\name(m, f)}
\Signature{(M, M -> List Vector R)}{List Vector R}
\Params{
{\em m} & M & A matrix\\
{\em f} & M -> List Vector R & A nullspace finder\\
}
\Retval{Returns a basis for the nullspace of m,
uses a specialized algorithm if m is overdetermined,
uses f when the system is no longer overdetermined.}
\Remarks{Can destroy a.}
#endif
} == add {
	local gcd?:Boolean	== R has GcdDomain;
	local prim!(v:V R):V R	== { gcd? => gcdprim! v; v; }

	if R has GcdDomain then {
		local gcdprim!(v:V R):V R == {
			import from I, R;
			n := #v;
			ASSERT(n > 0);
			g := v.1;
			for i in 2..n repeat {
				unit? g => return v;
				g := gcd(g, v.i);
			}
			if ~unit? g then for i in 1..n repeat
				v.i := quotient(v.i, g);
			v;
		}
	}

	-- return a matrix whose columns are the vectors in l
	local matrix(l:List V R):M == {
		import from I, V R;
		zero?(c := #l) => zero(0, 0);
		m:M := zero(r := #(first l), c);
		for j in 1..c for v in l repeat {
			ASSERT(#v = r);
			for i in 1..r repeat m(i, j) := v.i;
		}
		m;
	}


	-- reverses the order of l when multiplying on the left by m
	-- makes primitive if R is a gcd domain
	local (m:M) * (l:List V R):List V R == {
		ll:List V R := empty();
		for v in l repeat ll := cons(prim!(m * v), ll);
		ll;
	}

	-- split into odd and even rows
	local split(a:M):(M, M) == {
		import from I;
		(r, c) := dimensions a;
		ASSERT(r >= c + c); ASSERT(c > 0);
		r2 := r quo 2;
		m := { odd? r => next r2; r2 }
		o:M := zero(m, c);
		e:M := zero(r2, c);
		for i in 1..r2 repeat {
			i2 := i + i;
			for j in 1..c repeat {
				o(i, j) := a(prev i2, j);
				e(i, j) := a(i2, j);
			}
		}
		if odd? r then for j in 1..c repeat o(m, j) := a(r, j);
		(o, e);
	}

	nullSpace!(a:M, nullsp!:M -> List V R):List V R == {
		import from I;
		START__TIME;
		(r, c) := dimensions a;
		ASSERT(r > 0); ASSERT(c > 0);
		TRACE("overdet::nullspace: # of equations = ", r);
		TRACE("overdet::nullspace: # of unknowns = ", c);
		r < c + c => nullsp! a;
		(a, b) := split a;
		TIME("overdet::nullspace: split at ");
		k := nullSpace!(a, nullsp!);
		TIME("overdet::nullspace: half-nullspace at ");
		empty? k => k;
		b := b * (m := matrix k);
		zero? b => k;
		-- at this point k is not the true kernel,
		-- but a x = 0 is equivalent to x = m y and b y = 0
		k := nullSpace!(b, nullsp!);
		TIME("overdet::nullspace: y-nullspace at ");
		l := m * k;
		TIME("overdet::nullspace: x-nullspace at ");
		l;
	}
}
