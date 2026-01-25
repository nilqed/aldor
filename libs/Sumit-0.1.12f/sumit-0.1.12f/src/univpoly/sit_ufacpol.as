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
----------------------------- sit_ufacpol.as ----------------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I == MachineInteger;
	Z == Integer;
	TREE == ExpressionTree;
}

#if ALDOC
\thistype{UnivariateFactorialPolynomial}
\History{Manuel Bronstein}{16/6/2000}{created}
\Usage{ import from \this(R, Rx)}
\Params{
{\em R} & \astype{Ring} & The coefficient domain\\
{\em Rx} & \astype{UnivariatePolynomialCategory} R & A polynomial type over R\\
}
\Descr{\this(R, Rx) implements univariate factorial polynomials with
coefficients in $R$.
Those are polynomials with respect to the basis
of the descending factorials $(x^{{\underline n}})_{n \ge 0}$,
where $x^{{\underline n}} = x (x-1) \dots (x-n+1)$.
Rx is used for representing
the factorial polynomials, so you can choose between sparse and dense
representations.}
\begin{exports}
\category{\astype{UnivariateFreeFiniteAlgebra} R}\\
\asexp{coerce}: & Rx $\to$ \% & Conversion to a factorial polynomial\\
\asexp{expand}: & \% $\to$ Rx & Conversion from a factorial polynomial\\
\end{exports}
\begin{exports}[if $R$ has \astype{CommutativeRing} then]
\category{\astype{CommutativeRing}}\\
\end{exports}
#endif

UnivariateFactorialPolynomial(R:Ring, Rx: UnivariatePolynomialCategory R):
	UnivariateFreeFiniteAlgebra R with {
		if R has CommutativeRing then CommutativeRing;
		coerce: Rx -> %;
		expand: % -> Rx;
#if ALDOC
\aspage{coerce,expand}
\astarget{coerce}
\astarget{expand}
\Usage{p::\%\\ coerce~p\\ expand~q}
\Signatures{
coerce: & Rx $\to$ \%\\
expand: & \% $\to$ Rx\\
}
\Params{
{\em p} & Rx & A polynomial\\
{\em q} & \% & A factorial polynomial\\
}
\Descr{p::\% converts $p$ from the power basis $(x^n)_{n \ge 0}$ to
the factorial basis $(x^{{\underline n}})_{n \ge 0}$, while expand(q)
performs the reverse conversion.}
#endif
} == Rx add {
	local minus1:TREE			== extree(-$R(1$R))$R;
	local monom1:TREE			== extree(monom$Rx)$Rx;
	extree(p:%):TREE			== p monom1;
	(port:TextWriter) << (p:%): TextWriter	== tex(port, extree p);

	-- very naive for now
	(p:%) * (q:%):% == {
		import from Z, R;
		zero? p or zero? q => 0;
		one? p => q; one? q => p;
		dp := degree p; dq := degree q;
		prod:% := 0;
		for i in dp..0 by -1 repeat {
			for j in dq..0 by -1 repeat {
				c := coefficient(p, i) * coefficient(q, j);
				prod := add!(prod, c, xixj(i, j));
			}
		}
		prod;
	}

	expand(p:%):Rx == {
		import from R;
		zero? p => 0;
		x:Rx := monom;
		d := degree p;
		q:Rx := monomial(1, next d);	-- to allocate memory
		m:Z := 0;
		xm:Rx := 1 + q;			-- also allocates memory
		xm := add!(xm, -1, next d);	-- xm = 1 with space for x^{d+1}
		for term in terms p repeat {	-- in increasing order
			(c, n) := term;
			assert(n >= m);
			-- x^{_n_} = x^{_m_}(x-m)...(x-n+1)
			for i in m..prev n repeat xm := times!(xm, x - i::Rx);
			q := add!(q, c, xm);
			m := n;
		}
		-- add!(q, -1, next d);
		q := add!(q, -1, next d);
		q;
	}

	coerce(p:Rx):% == {
		import from R;
		zero? p => 0;
		d := degree p;
		q:% := monomial(1, next d);	-- to allocate memory
		m:Z := 0;
		xm:% := 1 + q;			-- also allocates memory
		xm := add!(xm, -1, next d);	-- xm = 1 with space for x^{d+1}
		for term in terms p repeat {	-- in increasing order
			(c, n) := term;
			assert(n >= m);
			-- if x^n = \sum_{i=0}^n a_i x^{_i_} then
			-- x^{n+1} = \sum_{i=0}^{n+1} (a_{i-1}+i a_i) x^{_i_}
			for i in m..prev n repeat {
				dp := differentiate(xm pretend Rx) pretend %;
				xm := shift!(add!(xm, dp), 1);
			}
			q := add!(q, c, xm);
			m := n;
		}
		add!(q, -1, next d);
	}

	apply(p:%, x:TREE):TREE == {
		import from Boolean, R;
		zero? p => extree(0@R);
		l:List(TREE) := empty;
		for term in p repeat {
			(c, n) := term;
			l := cons(tree(c, n, x), l);
		}
		assert(~empty? l);
		empty? rest l => first l;
		ExpressionTreePlus reverse! l;
	}

	local tree(c:R, n:Z, x:TREE):TREE == {
		import from Boolean, R, List TREE;
		assert(~zero? c);
		negative?(tc := extree c) =>
			ExpressionTreeMinus [tree(c ~= -1, negate tc, n, x)];
		tree(c ~= 1, tc, n, x);
	}

	local tree(tims?:Boolean, c:TREE, n:Z, x:TREE):TREE == {
		import from R, List TREE;
		zero? n => c;
		if n > 1 then x := ExpressionTreeFactorial [x,minus1,extree n];
		tims? => ExpressionTreeTimes [c, x];
		x;
	}

	-- Use the formula
	--   x^{{\underline i}} x^{{\underline j}} =
	--   \sum_{k=max(i,j)}^{i+j}
	--            j^{{\underline i+j-k}} {i \choose k-j} x^{{\underline k}}
	local xixj(i:Z, j:Z):% == {
		import from I, R;
		ans:% := 0;
		low := max(i, j);
		high := i + j;
		for k in high..low by -1 repeat {
			c := factorial(j,-1,machine(high-k)) * binomial(i,k-j);
			ans := add!(ans, c::R, k::Z);
		}
		ans;
	}
}
