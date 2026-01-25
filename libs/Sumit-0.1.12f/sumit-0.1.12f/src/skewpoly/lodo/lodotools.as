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
------------------------------ lodotools.as ------------------------------
#include "sumit"

macro Z == Integer;

#if ASDOC
\thistype{LinearOrdinaryDifferentialOperatorTools}
\History{Manuel Bronstein}{10/6/97}{created}
\Usage{ import from \this(R, L) }
\Params{
{\em R} & IntegralDomain & The coefficient ring\\
{\em L} & LinearOrdinaryDifferentialOperatorCategory R & The operators\\
}
\Descr{\this(R, L) implements some useful manipulations on the
elements of $L$.}
\begin{exports}
compose: & (L, R, R) $\to$ (L, R) & Compose operator with $D + a/b$\\
twist: & (L, Product R) $\to$ (L, R) &
Change of variable in a differential equation\\
\end{exports}
#endif

LinearOrdinaryDifferentialOperatorTools(R:IntegralDomain,
	L:LinearOrdinaryDifferentialOperatorCategory R): with {
		compose: (L, R, R) -> (L, R);
#if ASDOC
\aspage{compose}
\Usage{\name(p, a, b)}
\Params{
{\em p} & L & A differential operator\\
{\em a} & R & An element of the coefficient ring\\
{\em b} & R & A nonzero element of the coefficient ring\\
}
\Retval{Returns $({\overline p}, \alpha)$ such that
$$
{\overline p} = \alpha p\paren{\partial + \frac ab} =
\alpha \sum_{i=0}^n a_i \paren{\partial + \frac ab}^i
$$
where $p = \sum_{i=0}^n a_i \partial^i$,
and $\alpha \in R\setminus\{0\}$ is chosen so that
the result has coefficients in $R$.}
#endif
		twist: (L, Product R) -> (L, R);
#if ASDOC
\aspage{twist}
\Usage{\name(p, q)}
\Params{
{\em p} & L & A differential operator\\
{\em q} & Product R & A product of coefficients\\
}
\Retval{Returns $({\overline p}, \alpha)$ such that
$\deg({\overline p}) = \deg(p)$ and
$$
{\overline p} = \alpha p\paren{\partial - \frac {q'}q} =
\alpha \sum_{i=0}^n a_i \paren{\partial - \frac {q'}q}^i
$$
where $p = \sum_{i=0}^n a_i \partial^i$,
and $\alpha \in R\setminus\{0\}$ is chosen so that
the result has coefficients in $R$.
We have
$$
{\overline p}(y) = \alpha q p\paren{\frac yq}
$$
for any $y$ in any differential extension of $R$,
and in particular,
$$
{\overline p}(y) = 0 \iff p\paren{\frac yq} = 0\,.
$$
}
#endif
} == add {
	local gcd?:Boolean == R has GcdDomain;

	-- Returns (op', alpha) such that op' = alpha sum_i a_i (D - d'/d)^i
	-- has coefficients in R, where where op = sum_i a_i D^i
	-- We have op(z/d) = d^{-1} alpha^{-1} op'(z), so
	-- op(z/d) = 0  iff  op'(z) = 0, and
	-- op(z/d) = g  iff  op'(z) = d alpha g
	twist(op:L, d:Product R):(L, R) == {
		import from R;
		(a, b) := logarithmicDerivative d;
		compose(op, -a, b);
	}

	-- returns (a, b) s.t. d'/d = a/b
	local logarithmicDerivative(d:Product R):(R, R) == {
		import from R, Derivation R;
		dstar:R := 1;
		for term in d repeat {
			(p, n) := term;
			dstar := times!(dstar, p);
		}
		D := derivation$L;
		a:R := 0;
		for term in d repeat {
			(p, n) := term;
			a := add!(a, n * quotient(dstar, p) * D p);
		}
		(a, dstar);
	}

	if R has GcdDomain then {
		local gcdcompose(op:L, a:R, b:R):(L, R) == {
			import from Z, Partial R;
			(g, A, B) := gcdquo(a, b);
			failed?(u := reciprocal B) => {
				(opbar, n) := compose0(op, A, B);
				assert(n >= 0);
				(opbar, B^n);
			}
			(compose(op, monom + (A * retract u)::L), 1);
		}
	}

	-- returns (opbar, d) such that opbar = d sum_i a_i (D + a/b)^i
	-- has coefficients in R, where where op = sum_i a_i D^i
	compose(op:L, a:R, b:R):(L, R) == {
		import from Z, Partial R;
		assert(~zero? b);
		zero? a => (op, 1);
		gcd? => gcdcompose(op, a, b);
		failed?(u := exactQuotient(a, b)) => {
			(opbar, n) := compose0(op, a, b);
			assert(n >= 0);
			(opbar, b^n);
		}
		(compose(op, monom + retract(u)::L), 1);
	}

	macro {
		Rb == QuotientBy(R, b, false);
		Lb == LinearOrdinaryDifferentialOperator(Rb, D);
	}

	local compose0(op:L, a:R, b:R):(L, Z) == {
		import from Rb;
		(opbar, n) := compose0(op, a, b, lift(derivation$L));
		n < 0 => (b^(-n) * opbar, 0);
		(opbar, n);
	}

	-- all simplifications have failed, a/b is not in R
	-- returns (opbar, n) such that opbar = b^n L(D + a/b) has coeffs in R
	local compose0(op:L, a:R, b:R, D:Derivation Rb):(L, Z) == {
		assert(~unit? b);
		import from Z, Rb, Lb;
		outside := next degree op;
		pq:Lb := monomial(1, outside);		-- to allocate space
		q:Lb := monom + shift(a::Rb, -1)::Lb;	-- q = D + a/b
		qn:Lb := 1;
		d:Z := 0;
		for term in reverse op while ~zero?(qn) repeat {
			(c, n) := term;
			for i in 1..n - d repeat qn := q * qn;
			pq := add!(pq, c::Rb * qn);
			d := n;
		}
		pq := add!(pq, -1, outside);	-- remove extra term
		ans:L := 0;			-- pq is the true composition
		zero? pq => (ans, 0);
		m:Z := order leadingCoefficient pq;
		for bterm in reductum pq repeat {
			(bc, n) := bterm;
			n := order bc;
			if n < m then m := n;
		}
		m := -m;
		for bterm in pq repeat {	-- compute b^m pq
			(bc, n) := bterm;
			bc := shift(bc, m);
			assert(one? denominator bc);
			ans := add!(ans, numerator bc, n);
		}
		(ans, m);
	}
}

