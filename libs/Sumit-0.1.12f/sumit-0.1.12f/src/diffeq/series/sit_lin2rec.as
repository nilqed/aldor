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
------------------------------ sit_lin2rec.as ------------------------------
-- Copyright (c) Manuel Bronstein 1997
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I	== MachineInteger;
	Z	== Integer;
	A	== Array;
	V	== Vector;
	M	== DenseMatrix;
	SYS	== LinearOrdinaryFirstOrderSystem Rx;
}

#if ALDOC
\thistype{LinearOrdinaryOperatorToRecurrence}
\History{Manuel Bronstein}{3/11/97}{created}
\Usage{ import from \this(R, Rx, Rxy, Rxe);}
\Params{
{\em R} & \astype{CommutativeRing} & A commutative ring\\
{\em Rx} & \astype{UnivariatePolynomialCategory} R & Polynomials over R\\
{\em Rxy} & \astype{UnivariateSkewPolynomialCategory} Rx & Operators over Rx\\
{\em Rxe} & \astype{LinearOrdinaryRecurrenceCategory} Rx &
Recurrence operators over Rx\\
}
\Descr{\this(R, Rx, Rxy, Rxe) provides conversions from linear operators
to recurrences.}
\begin{exports}
\asexp{drop}: & Rxy $\to$ \astype{Integer} & degree drop\\
\asexp{recurrence}:
& Rxy $\to$ (Rxe, \astype{Integer}) & recurrence for some basis\\
& SYS Rx $\to$ (\astype{Array} \astype{DenseMatrix} Rx, \astype{Integer}) & \\
\end{exports}
\begin{aswhere}
SYS &==& \astype{LinearOrdinaryFirstOrderSystem}\\
\end{aswhere}
#endif

LinearOrdinaryOperatorToRecurrence(R:CommutativeRing,
	Rx:  UnivariatePolynomialCategory R,
	Rxy: UnivariateSkewPolynomialCategory Rx,
	Rxe: LinearOrdinaryRecurrenceCategory Rx): with {
		drop: Rxy -> Z;
#if ALDOC
\aspage{drop}
\Usage{\name~L}
\Signature{Rxy}{\astype{Integer}}
\Params{ {\em L} & Rxy & A differential or difference operator\\ }
\Retval{Returns $n$ such that for any nonzero $p$ in $Rx$,
either $L p = 0$ or $\deg(L p) \le \deg(p) - n$.}
\Remarks{Produces an error if $L$ is neither a differential or recurrence
operator.}
#endif
		recurrence: Rxy -> (Rxe, Z);
		recurrence: SYS -> (A M Rx, Z);
#if ALDOC
\aspage{recurrence}
\Usage{\name~L\\ \name~S}
\Signatures{
\name: & Rxy $\to$ (Rxe, \astype{Integer})\\
\name: &
SYS Rx $\to$ (\astype{Array} \astype{DenseMatrix} Rx, \astype{Integer})\\
}
\begin{aswhere}
SYS &==& \astype{LinearOrdinaryFirstOrderSystem}\\
\end{aswhere}
\Params{
{\em L} & Rxy & A differential or difference operator\\
{\em S} & SYS Rx & A first order differential or difference system\\
}
\Descr{\name(L) returns
$(R = \sum_i a_i E^i, m)$
such that for any formal series
solution $\sum_{n >= 0} z_n P_n$ of $L y = 0$
the sequence $(z_0,z_1,\dots)$ is a solution of
$$
\paren{\sum_i a_i E^{i+m}} z = R E^m z = 0\,,
$$
while \name(S) returns $([A_0,\dots,A_d], m)$
such that for any formal series
solution $\sum_{n >= 0} Z_n P_n$ of $S Y = 0$,
the sequence $(Z_0,Z_1,\dots)$ is a solution of
$$
\paren{\sum_i A_i E^{i+m}} Z = 0\,.
$$
In both cases,
the basis $P_n$ is $P_n = x^n$ when $L$ or $S$ is a differential operator,
and $P_n = x^{{\underline n}} = x (x-1) \dots (x-n+1)$ when $L$ or $S$ is
a recurrence operator.
}
\Remarks{Produces an error if $L$ or $S$
is neither a differential or recurrence operator.}
#endif
	simple: SYS -> Partial Rx;
} == add {
	-- The results are normalized so that A_0 is not identically 0
	recurrence(L:SYS):(A M Rx, Z) == {
		import from Boolean, I, Z, M Z, M Rx, Rxe, M Rxe;
		(r, m) := recsys L;
		n := machine order L;
		assert(n > 0);
		b := m(1, 1);		-- will be min(m_ij)
		d:Z := 0;		-- will be max(deg(r_ij) - m_ij)
		fresh? := true;
		for i in 1..n repeat for j in 1..n repeat {
			bb := m(i, j);
			if bb < b then b := bb;
			if ~zero?(rec := r(i, j)) then {
				dd := degree(rec) + bb;
				if fresh? then { d := dd; fresh? := false }
				else { if dd > d then d := dd }
			}
		}
		assert(~fresh?);	-- some recurrence must be nonzero
		deg := machine(d - b);	-- degree of the matrix-recurrence
		v:A M Rx := new next deg;
		for i in 0..deg repeat v.i := zero(n, n);
		for i in 1..n repeat for j in 1..n repeat {
			k := machine(m(i, j) - b);
			for term in r(i, j) repeat {
				(p, e) := term;
				v(k + machine e)(i, j) := p;
			}
		}
		j:I := 0;
		while zero?(v.j) repeat j := next j;
		zero? j => (v, b);
		([v.i for i in j..deg], b + j::Z);
	}

	local recsys(L:SYS):(M Rxe, M Z) == {
		import from I, Z, V Rx, M Rx, Rxy;
		(d, a) := matrix L;
		n := machine order L;
		mat:M Rxe := zero(n, n);
		bmat:M Z := zero(n, n);
		for i in 1..n repeat for j in 1..n repeat {
			op := - a(i, j)::Rxy;
			if i = j then op := op + monomial(d.i, 1);
			(rec, b) := recurrence op;
			mat(i, j) := rec;
			bmat(i, j) := b;
		}
		(mat, bmat);
	}

	local whichType():MachineInteger == {
		x:Rx := monom;
		p:Rxy := monom;
		p(1, x) = x + 1 => {		-- sigma(x) + delta(x) = x + 1
			d := p(0, x);		-- delta(x)
			zero? d => -1;		-- x -> x+1, recurrence
			one? d => 1;		-- d/dx, differential
			0;			-- all others
		}
		0;				-- all others
	}

	local which:MachineInteger == whichType();

	drop(L:Rxy):Z == {
		import from String;
		which > 0 => minOrder L;
		which < 0 => - maxDegree L;
		error "drop:expect a differential or difference operator";
	}

	recurrence(L:Rxy):(Rxe, Z) == {
		import from String;
		zero? L => (0, 0);
		which > 0 => recurrenceD L;
		which < 0 => recurrenceE L;
		error "recurrence:expect a differential or difference operator";
	}

	simple(L:SYS):Partial Rx == {
		import from String;
		which > 0 => failed;	-- TEMPORARY: not yet implemented
		which < 0 => simpleE L;
		error "simple:expect a differential or difference operator";
	}

	-- Computes the integer b and the operator p(L) such that
	--       R(L) = p(L) E^b
	-- where R(L) is the recurrence corresponding to L for the
	-- power basis (x^n)_{n \ge 0}, as described in:
	-- S.A.Abramov, M.Petkovsek, A.Ryabenko,
	--    "Special formal series solutions of linear operator equations"
	-- Discrete Mathematics 210 (2000) 3--25.
	-- R(L)is obtained through the substitutions
	--             x -> E^{-1}         D -> (n+1) E
	-- The closed form formulas we use for b and p(L) are:
	--   b    = min_j(j - deg_x(p_j))
	--   p(L) = \sum_j \sum_i a_ji (n + 1 - i)^{\bar j} E^{j - i - b}
	-- where x^{\bar j} is the ascending factorial of degree j
	-- and   L = \sum_j (\sum_i a_ji x^i) D^j
	-- The results are normalized so that p(L) has trailing degree 0
	local recurrenceD(L:Rxy):(Rxe, Z) == {
		import from MachineInteger, Z;
		b := drop L;
		r:Rxe := 0;
		n:Rx := monom;
		for term in L repeat {
			(p, j) := term;
			jj := machine j;
			for pterm in p repeat {
				(a, i) := pterm;
				r := add!(r, a * factorial(n+(1-i)::Rx, 1, jj),
						j - i - b);
			}
		}
		zero?(d := trailingDegree r) => (r, b);
		assert(d > 0);
		(shift(r, -d), b+d);
	}

	-- returns min(n - deg(coeff(L,n),x)) over the coeffs of L
	local minOrder(L:Rxy):Z == {
		import from Rx;
		b := degree L - degree leadingCoefficient L;
		for term in reductum L repeat {
			(p, n) := term;
			m := n - degree p;
			if m < b then b := m;
		}
		b;
	}

	-- Computes the integer b and the operator p(L) such that
	--       R(L) = p(L) E^b
	-- where R(L) is the recurrence corresponding to L for the
	-- fractional power basis (x^{\bar n})_{n \ge 0}
	-- where x^{\bar j} is the descending factorial of degree j
	-- R(L)is obtained through the substitutions
	--            x -> (n + E^{-1})      E -> (1 + (n+1) E) 
	-- The closed form formulas we use for b and p(L) are:
	--   b    = - max_j(deg_x(p_j))
	--   p(L) = \sum_j \sum_i P_i \kappa_{\sigma^{-i}} Q_j E^{-i-b}
	-- where L = \sum_j (\sum_i a_ji x^i) E^j and P_i, Q_j are given by
	-- P_0 = 1, P_{i+1} = n P_i E + \kappa_{\sigma^{-1}} P_i,
	-- Q_j = (1 + (n+1) E)^j  and
	--    \kappa_f(\sum_k a_k E^k) = \sum_k f(a_k) E^k
	-- The results are normalized so that p(L) has trailing degree 0
	local recurrenceE(L:Rxy):(Rxe, Z) == {
		import from MachineInteger, Z;
		b := drop L;
		bb := - machine b;
		n:Rx := monom;
		f:PrimitiveArray(Rxe -> Rxe) := new next bb;
		f.0 := map(sigma 0);
		P:PrimitiveArray Rxe := new next bb;
		P.0 := 1;
		for i in 1..bb repeat {
			f.i := map(sigma(-i::Z));
			P.i := n * shift(P(prev i), 1) + (f.1)(P prev i);
		}
		d := degree L;
		dd := machine d;
		Q:PrimitiveArray Rxe := new next dd;
		Q.0 := 1;
		if dd > 0 then {
			Q.1 := monomial(n + 1, 1) + 1;
			for j in 2..dd repeat Q.j := Q.1 * Q(prev j);
		}
		r:Rxe := 0;
		for term in L repeat {
			(p, jj) := term;
			j := machine jj;
			for pterm in p repeat {
				(a, k) := pterm;
				i := machine k;
				r := add!(r,shift((a::Rx)*P.i*(f.i)(Q.j),-k-b));
			}
		}
		zero?(d := trailingDegree r) => (r, b);
		assert(d > 0);
		(shift(r, -d), b+d);
	}

	local sigma(n:Z):Rx -> Rx == {
		import from Rx;
		zero? n => { (p:Rx):Rx +-> p }
		q := monom + n::Rx;
		(p:Rx):Rx +-> p q;
	}

	-- returns max(deg(coeff(L,n),x)) over the coeffs of L
	local maxDegree(L:Rxy):Z == {
		import from Rx;
		b := degree leadingCoefficient L;
		for term in reductum L repeat {
			(p, n) := term;
			m := degree p;
			if m > b then b := m;
		}
		b;
	}

	-- returns an equation for the degree of the polynomial solutions
	-- if the system if simple at infinity, failed otherwise
	local simpleE(L:SYS):Partial Rx == {
		import from Boolean, I, Z;
		import from Rx, V Rx, M Rx, LinearAlgebra(Rx, M Rx);
		(a, m) := matrix L;	-- a Y(x+1) = m Y(x)...
		-- a Y(x+1) = m Y(x) <=> x (Y(x+1) - Y(x)) = a^{-1} x (m-a) Y(x)
		-- so the matrix M(x) in eq (2) of Abramov & Barkatou ISSAC'98
		-- is  M = a^{-1} x (m - a)
		n := machine order L;
		alpha:V Z := zero n;
		b := copy m;
		for i in 1..n repeat {			-- compute the alpha.i
			b(i,i) := b(i,i) - a.i;		-- b = m - a
			assert(~zero?(a.i));
			d := degree(a.i);
			for j in 1..n | ~zero?(b(i,j)) repeat {
				dd := next(degree(b(i,j))) - d;	-- ie -ord(M_ij)
				if dd > alpha.i then alpha.i := dd;
			}
		}
		TRACE("rcplsys::indicialEquation: alpha = ", alpha);
		-- D = diag(x^{-alpha.i}) and A = a^{-1} D (m - a)
		--                              = a^{-1} diag(x^{1 - alpha.i}) b
		mt := zero(n, n);
		for i in 1..n repeat {
			d := degree(a.i);
			al := alpha.i;
			for j in 1..n | ~zero?(b(i,j)) repeat {
				if next(degree(b(i,j))) = al + d then
					mt(i,j):=leadingCoefficient(b(i,j))::Rx;
			}
			if zero?(alpha.i) then
				mt(i,i) := mt(i,i)
					- monomial(leadingCoefficient(a.i), 1);
		}
		(rank?, rk) := rankLowerBound mt;
		rk = n => [determinant mt];
		failed;
	}
}
