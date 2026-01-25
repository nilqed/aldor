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
--------------------------- sit_polkara.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1996
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1996-97
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I == MachineInteger;
	Z == Integer;
	A == PrimitiveArray R;
}

#if ALDOC
\thistype{UnivariatePolynomialKaratsuba}
\History{Manuel Bronstein}{6/12/96}{created}
\Usage{ import from \this~R }
\Params{
{\em R} & \astype{CommutativeRing} & The coefficient ring of the polynomials\\
}
\Descr{\this~R implements Karatsuba multiplication for dense univariate
polynomials with coefficients in R.}
\begin{exports}
\asexp{karatsuba!}: & (A, A, Z, A, Z, Z, (A, A, Z, A, Z) -> ()) $\to$ () &
Karatsuba multiplication\\
\end{exports}
\begin{aswhere}
A &==& \astype{PrimitiveArray} R\\
Z &==& \astype{MachineInteger}\\
\end{aswhere}
#endif

UnivariatePolynomialKaratsuba(R:CommutativeRing): with {
	karatsuba!: (A, A, I, A, I, I, times!:(A, A, I, A, I) -> ()) -> ();
} == add {
	local intdom?:Boolean == R has IntegralDomain;

	local zero?(c:A, d:I):Boolean == {
		import from R;
		zero? d and zero?(c.0);
	}

	-- global buffer for karatsuba: only grows as needed so we do
	-- not have to allocate a new work buffer for each product.
	-- store the size whether buf is an array or primitive array
	macro REC			== Record(siz:I, deg:I, buf:A);
	local karaWork:REC		== [1, 0, new 1];

	local karaWorkBuffer(n:I, cut:I):A == {
		import from REC;
		assert(n >= cut);
		buffer := karaWork.buf;
		n <= karaWork.deg => buffer;	-- existing buffer is sufficient
		karaWork.deg := n;
		-- compute the amount of storage needed
		m:I := 0;
		while n >= cut repeat {
			n := next(n quo 2);
			m := m + 2 * n;
			n := prev n;
		}
		TRACE("karatsuba: size needed for work buffer = ", m);
		sz := karaWork.siz;
		m <= sz => buffer;
		-- buffer := resize!(buffer, sz, m);
		free!(karaWork.buf);
		buffer := new m;
		karaWork.buf := buffer;
		karaWork.siz := m;
		buffer;
	}

	-- compute the low+high words of c in cc, both have degrees < e
	-- d = degree c, returns the degree of the sum  c_low + c_high
	local addlowhigh!(cc:A, c:A, d:I, e:I):I == {
		import from R;
		assert(next(d) <= 2*e);
		for i in 0..prev e repeat cc.i := c.i;
		for i in e..d repeat cc(i - e) := cc(i - e) + c.i;
		computeDegree(prev e, cc);
	}

	-- adds q to p, dq = degree q, p must be large enough
	local add!(p:A, q:A, dq:I):() == {
		import from R;
		for i in 0..dq repeat p.i := p.i + q.i;
	}

	-- substracts q from p, dq = degree q, p must be large enough
	local sub!(p:A, q:A, dq:I):() == {
		import from R;
		for i in 0..dq repeat p.i := p.i - q.i;
	}

	-- zeroes p up to terms of degree d
	local zero!(p:A, d:I):() == {
		import from R;
		for i in 0..d repeat p.i := 0;
	}

	karatsuba!(pq:A,p:A,dp:I,q:A,dq:I,cut:I,times!:(A,A,I,A,I)->()):() ==
		karatsuba!(pq, p, dp, q, dq, cut,
				karaWorkBuffer(max(dp, dq), cut), times!);

	-- pq = pq + p q
	-- cut = degree cutoff (use quadratic multiplication below)
	local karatsuba!(pq:A, p:A, dp:I, q:A, dq:I, cut:I, work:A,
					times!:(A, A, I, A, I) -> ()):() == {
		TRACE("karatsuba!: p = ", p);
		TRACE("karatsuba!: dp = ", dp);
		TRACE("karatsuba!: q = ", q);
		TRACE("karatsuba!: dq = ", dq);
		TRACE("karatsuba!: cut = ", cut);
		if dp < dq then (p, dp, q, dq) := (q, dq, p, dp);
		assert(dp >= dq);
		dp < cut => times!(pq, p, dp, q, dq);
		m := next(dp quo 2);
		TRACE("karatsuba!: m = ", m);
		assert(2 * m > dp);
		assert(2 * prev m <= dp);
		dpl := computeDegree(prev m, p);	-- dpl = degree(pl)
		TRACE("karatsuba!: degree p_l = ", dpl);
		m > dq => {				-- p q = pl q + x^m ph q
			if ~zero?(p, dpl) then		-- pq = pq + pl q
				karatsuba!(pq, p, dpl, q, dq, cut, work,times!);
			karatsuba!(pq+m, p+m, dp - m, q, dq, cut, work, times!);
		}
		m2 := 2 * m;
		dpsum := addlowhigh!(work, p, dp, m);		-- pl + ph
		dqsum := addlowhigh!(work + m, q, dq, m);	-- ql + qh
		-- compute x^m (pl + ph) (ql + qh) = x^m c
		karatsuba!(pq+m,work,dpsum,work+m,dqsum,cut,work+m2,times!);
		dql := computeDegree(prev m, q);	-- dql = degree(ql)
		TRACE("karatsuba!: degree q_l = ", dql);
		dplql := dpl + dql;
		assert(dplql <= dp);
		zero!(work, dplql);
		if ~(zero?(p, dpl) or zero?(q, dql)) then {	-- pl ql
			karatsuba!(work,p,dpl,q,dql,cut,work+next dplql,times!);
			if ~intdom? then dplql := computeDegree(dplql, work);
			sub!(pq + m, work, dplql);	-- x^m (c - plql)
			add!(pq, work, dplql);		-- add x^0 pl ql
		}
		dphqh := dp + dq - m2;
		assert(dphqh <= dp);
		zero!(work, dphqh);
		karatsuba!(work,p+m,dp-m,q+m,dq-m,cut,work+next dphqh,times!);
		if ~intdom? then dphqh := computeDegree(dphqh, work);
		sub!(pq + m, work, dphqh);		-- x^m (c - plql - phqh)
		add!(pq + m2, work, dphqh);		-- + x^{2m} ph qh
	}

	-- n = upper bound on the actual degree
	local computeDegree(n:I, c:A):I == {
		assert(n >= 0);
		import from R;
		for i in n..0 by -1 repeat ~zero?(c.i) => return i;
		0;
	}
}
