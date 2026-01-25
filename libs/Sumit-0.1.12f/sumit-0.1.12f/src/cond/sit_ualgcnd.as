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
----------------------------  sit_ualgcnd.as   ------------------------------
-- Copyright (c) Marco Codutti 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{UnivariateAlgebraicCondition}
\History {Marco Codutti}{20 June 95}{created}
\History {Manuel Bronstein}{16/11/99}{redesigned}
\Usage   {import from \this(R,Rx)}
\Params{
{\em R} & \astype{GcdDomain} & The coefficient domain\\
{\em Rx} & \astype{UnivariatePolynomialCategory} R & A polynomial type over R\\
}
\Descr{\this(R,Rx)~implements algebraic conditions on one parameter.}
\begin{exports}
\category{\astype{EqualityCondition}}\\
\end{exports}
#endif

macro {
	B == Boolean;
	P == Product Rx;
	Z == Integer;
	TREE == ExpressionTree;
}

UnivariateAlgebraicCondition(R:GcdDomain, Rx:UnivariatePolynomialCategory R):
	EqualityCondition Rx == add {
	-- condition is prod = 0 si zro? is true, prod != 0 otherwise
	Rep == Record(prod:P, zro?:B);

	import from P;

	local cond(p:P, z?:B):%	== { import from Rep; per [p, z?]; }
	local zcond(p:P):%	== { import from B; cond(p, true) }
	local nzcond(p:P):%	== { import from B; cond(p, false) }
	local eq?(c:%):B	== { import from Rep; rep(c).zro? }
	local ineq?(c:%):B	== { import from Rep; ~(rep(c).zro?) }
	local product(c:%):P	== { import from Rep; rep(c).prod }
	Always:%		== nzcond 1;	-- 1 != 0
	Never:%			== zcond 1;	-- 1 = 0
	always?(c:%):B		== ineq? c and one? product c;
	never?(c:%):B		== eq? c and one? product c;
	~(c:%):%		== { import from B; cond(product c, ~eq? c) }
	copy(c:%):%		== { import from P; cond(copy product c,eq? c) }
	local tzero:TREE	== { import from R; extree 0; }
	local talways:TREE == { import from String, Symbol; extree(-"always") }
	local tnever:TREE  == { import from String, Symbol; extree(-"never") }

	zero(c:%):Generator Rx == generate {
		import from Z, Rx, P;
		if eq? c then for term in product c repeat {
			(p, n) := term;
			if degree p > 0 then yield p;
		}
	}

	nonzero(c:%):Generator Rx == generate {
		import from Z, Rx, P;
		if ineq? c then for term in product c repeat {
			(p, n) := term;
			if degree p > 0 then yield p;
		}
	}

	-- very inefficient for now
	(c1:%) = (c2:%):B == {
		eq? c1 => eq? c2 and product c1 = product c2;
		ineq? c2 and product c1 = product c2;
	}

	(p1:Rx) = (p2:Rx):% == {
		zero?(z := p1 - p2) => Always;
		zcond sqfr z;
	}

	(p1:Rx) ~= (p2:Rx):% == {
		zero?(z := p1 - p2) => Never;
		nzcond sqfr z;
	}

	local sqfr(p:Rx):P == {
		import from B, Z;
		assert(~zero? p);
		zero? degree p => 1;
		(c, prod) := squareFree p;
		q:P := 1;
		for term in prod repeat {
			(h, n) := term;
			q := times!(q, h, 1);
		}
		q;
	}

	split(c:%, p:Rx):(%, %) == {
		import from Rx;
		never? c => (c, c);
		zero? p => (c, Never);
		prod := sqfr p;
		always? c => (zcond prod, nzcond prod);
		-- inefficient for now
		pc := expand product c;
		pp := expand prod;
		(g, yc, yp) := gcdquo(pc, pp);
		ineq? c => (yp ~= 0, quotient(pc * pp, g) ~= 0);
		assert(eq? c);
		(g = 0, yc = 0);
	}

	(c1:%) /\ (c2:%):% == {
		import from Rx;
		never? c1 or never? c2 => Never;
		always? c1 => c2;
		always? c2 => c1;
		-- inefficient for now
		p1 := expand product c1;
		p2 := expand product c2;
		ineq? c1 => {
			ineq? c2 => lcm(p1, p2) ~= 0;
			(g, y1, y2) := gcdquo(p1, p2);
			y2 = 0;
		}
		assert(eq? c1);
		eq? c2 => gcd(p1, p2) = 0;
		(g, y1, y2) := gcdquo(p1, p2);
		y1 = 0;
	}

	(c1:%) \/ (c2:%):% == {
		import from Rx;
		always? c1 or always? c2 => Always;
		never? c1 => c2;
		never? c2 => c1;
		-- inefficient for now
		p1 := expand product c1;
		p2 := expand product c2;
		eq? c1 => {
			eq? c2 => lcm(p1, p2) = 0;
			(g, y1, y2) := gcdquo(p1, p2);
			y2 ~= 0;
		}
		assert(ineq? c1);
		ineq? c2 => gcd(p1, p2) ~= 0;
		(g, y1, y2) := gcdquo(p1, p2);
		y1 ~= 0;
	}

	extree(c:%):TREE == {
		import from P, List TREE;
		always? c => talways;
		never? c => tnever;
		e := extree product c;
		eq? c => ExpressionTreeEqual [e, tzero];
		ExpressionTreeNotEqual [e, tzero];
	}
}

#if SUMITTEST
-------------------------   test for sit_ualgcnd.as   -----------------------
#include "sumittest"

macro {
	Z == Integer;
	P == DenseUnivariatePolynomial Z;
	C == UnivariateAlgebraicCondition(Z, P);
}

local split():Boolean == {
	import from Z,P,C;

	a := monom;
	p:P := (a-1)*(a-2::P);
	c:C := p*(a+1)=0;
	(cp,cnp) := split(c,p);
	cp ~= (p = 0) => false;
	for nz in nonzero cnp repeat return false;
	i:Z := 0;
	for z in zero cnp repeat {
		degree z ~= 1 => return false;
		coefficient(z, 0) ~= leadingCoefficient z => return false;
		i := next i;
	}
	one? i;
}

stdout << "Testing sit__ualgcnd..." << endnl;
sumitTest("split", split);
stdout << endnl;
#endif
