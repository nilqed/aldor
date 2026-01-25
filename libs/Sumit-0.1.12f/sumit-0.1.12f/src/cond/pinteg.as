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
------------------------------  pinteg.as ---------------------------------
--
-- Integration of univariate fractions involving one parameter
--

#include "sumit"

#library param "psqfr.ao"
import from param;

macro {
	Z	== Integer;
	Symbol	== String;
	Ra	== DenseUnivariatePolynomial(R, var);
	Rab	== DenseUnivariatePolynomial(Ra, "b");
	Raxy	== DenseUnivariatePolynomial Rax;
	Rabx	== DenseUnivariatePolynomial Rab;
	Qa	== Quotient Ra;
	Qax	== DenseUnivariatePolynomial Qa;
	Q	== Quotient Qax;
	COND	== AlgebraicCondition(R, var);
	PR	== Product Rax;
	F	== Quotient Rax;
	Rx	== Quotient RX;
	RXY	== DenseUnivariatePolynomial RX;
	IR	== IntegrationResult(R, var, Rax);
}

Pair(T1:SumitType, T2:SumitType):SumitType with {
	pair: (T1, T2) -> %;
	explode: % -> (T1, T2);
} == add {
	macro Rep == Record(a:T1, b:T2);
	import from T1, T2, Rep;

	sample:%		== pair(sample, sample);
	explode(p:%):(T1, T2)	== explode rep p;
	pair(a:T1, b:T2):%	== per [a, b];

	extree(p:%):ExpressionTree == {
		import from List ExpressionTree;
		(a,b) := explode p;
		ExpressionTreeList [extree a, extree b];
	}

	(p:%) = (q:%):Boolean == {
		(a,b) := explode p;
		(c,d) := explode q;
		a = c and b = d;
	}
}

-- SAE's do not propagage char 0?
-- HermiteIntegration(R:Join(SumitField, CharacteristicZero),
HermiteIntegration(R:GcdDomain, RX:UnivariatePolynomialCategory R): with {
	lrt: (RX, RX) -> List Pair(RX, RXY);
	if R has SumitField then {
		hermite: (RX, RX, Product RX) -> (Rx, Rx);
	}
} == add {
	-- transforms \sum_i a_i x^i into \sum_i a_i y^i
	local RX2RXY(p:RX):RXY == {
		q:RXY := 0;
		for term in p repeat {
			(c, n) := term;
			q := add!(q, c::RX, n);
		}
		q;
	}

	local find(n:Z, l:List RXY):RXY == {
		assert(n > 0);
		for p in l repeat { degree p = n => return p }
		error "lazard/rioboo/trager: no subresultant of correct degree";
	}

	lrt(a:RX, d:RX):List Pair(RX, RXY) == {
		import from Z, RXY, List RXY, Product RX, Resultant(RX, RXY);
		l := SPRS(RX2RXY d,
				RX2RXY(a) - monom$RX * RX2RXY differentiate d);
		assert(~empty? l);	-- first element is the resultant
		r := first l;		-- involves x only
		assert(zero? degree r);
		ans:List Pair(RX, RXY) := empty();
		(cont, sq) := squareFree leadingCoefficient r;
		for term in sq repeat {
			(c, n) := term;
			ans := cons(pair(c, find(n, l)), ans);
		}
		ans;
	}

	if R has SumitField then {
	hermite(a:RX, d:RX, fd:Product RX):(Rx, Rx) == {
		import from Z, R, Rx, Partial Cross(RX, RX);
		g:Rx := 0;
		TRACE("hermite: a = ", a);
		TRACE("hermite: d = ", d);
		TRACE("hermite: fd = ", fd);
		for term in fd repeat {
			(v, m) := term;
			TRACE("hermite: v = ", v);
			TRACE("hermite: m = ", m);
			if m > 1 then {
				-- bug in SAE
				-- u := quotient(d, v^m);
				u := d quo v^m;
				TRACE("hermite: u = ", u);
				for j in prev(m)..1 by -1 repeat {
					TRACE("hermite: j = ", j);
					m1j := inv(-j::R);
					uvp := u * differentiate v;
					TRACE("hermite: uvp = ", uvp);
					w := extendedEuclidean(uvp, v, m1j * a);
					failed? w => error "Hermite:EEA failed";
					(b, e) := retract w;
					TRACE("hermite: b = ", b);
					TRACE("hermite: e = ", e);
					g := g + b / v^j;
					a := - j * e - u * differentiate b;
				}
				d := u * v;
			}
		}
		(g, a / d);
	}
	}
}

IntegrationResult(R:Join(SumitField, CharacteristicZero),
        var:Symbol, Rax:UnivariatePolynomialCategory Ra): SumitType with {
		ir: F -> %;
		ir: (F, List Pair(Rax, Raxy)) -> %
} == add {
	macro Rep == Record(alg:F, log:List Pair(Rab, Rabx)); 

	sample:% == { import from F; ir sample }
	ir(f:F):% == { import from List Pair(Rax, Raxy); ir(f, empty()) }
	local algPart(r:%):F == { import from Rep; rep(r).alg }
	local logPart(r:%):List Pair(Rab,Rabx) == { import from Rep;rep(r).log }

	ir(f:F, l:List Pair(Rax, Raxy)):% == {
		import from Rep, Pair(Rax, Raxy);
		import from Pair(Rab, Rabx), List Pair(Rab, Rabx);
		ll:List Pair(Rab, Rabx) := empty();
		for pq in l repeat {
			(p, q) := explode pq;
			ll := cons(pair(p pretend Rab, q pretend Rabx), ll);
		}
		per [f, ll];
	}

	extree(r:%):ExpressionTree == {
		import from F, List Pair(Rab, Rabx), List ExpressionTree;
		l := logPart r;
		zero?(a := algPart r) => {
			empty? l => extree(0$F);
			extree l;
		}
		e := extree a;
		empty? l => e;
		ExpressionTreePlus [e, extree l];
	}

	local extree(l:List Pair(Rab, Rabx)):ExpressionTree == {
		import from Pair(Rab, Rabx), List ExpressionTree;
		assert(~empty? l);
		ExpressionTreeList [extree pq for pq in l];
	}

	(r:%) = (s:%):Boolean == {
		import from SingleInteger,F,Pair(Rab,Rabx),List Pair(Rab,Rabx);
		algPart r ~= algPart s => false;
		#logPart(r) ~= #logPart(s) => false;
		for x in logPart r for y in logPart s repeat {
			x ~= y => return false;
		}
		true;
	}
}

ParametricUnivariateFractionIntegration(R:Join(SumitField, CharacteristicZero),
	var:Symbol, Rax:UnivariatePolynomialCategory Ra): with {
		hermiteCase: (F, c:COND == Always()) -> Case(COND, Pair(F, F));
		intCase: (F, c:COND == Always()) -> Case(COND, IR);
} == add {
	hermiteCase(f:F, c:COND):Case(COND, Pair(F, F)) == {
		import from Case(COND, PR), If(COND, Pair(F, F));
		import from ParametricUnivariatePolynomialSquareFree(R,var,Rax);
		ans:Case(COND, Pair(F, F)) := empty();
		a := numerator f;
		for sq in sqfrCase(d := denominator f, c) repeat {
			cq := condition sq;
			ans := addNewCase!(ans, [cq,hermite(a,d,object sq,cq)]);
		}
		ans;
	}

	intCase(f:F, c:COND):Case(COND, IR) == {
		import from If(COND, IR), Pair(F, F), Case(COND, Pair(F, F));
		ans:Case(COND, IR) := empty();
		for her in hermiteCase(f, c) repeat {
			ch := condition her;
			(g, h) := explode object her;
			ans := addNewCase!(ans, [ch, int(g, h, ch)]);
		}
		ans;
	}

	local int(g:F, h:F, c:COND):IR == {
		import from List Pair(Rax, Raxy), HermiteIntegration(Ra, Rax);
		import from ParametricUnivariatePolynomialSquareFree(R,var,Rax);
		import from UnivariateFreeAlgebraOverQuotient(Ra, Rax, Qa, Qax);
		zero? h => ir g;
		a := numerator h;
		d := denominator h;
		zeroCase? c => int(g, a, d, poly c);
		ir(g, lrt(a, d));
	}

	local int(g:F, a:Rax, d:Rax, p:Ra):IR == {
		macro E == SimpleAlgebraicExtension(R, Ra, p);
		macro Ex == DenseUnivariatePolynomial E;
		macro Exy == DenseUnivariatePolynomial Ex;
		import from F, Ex, Quotient Ex;
		import from HermiteIntegration(E, Ex);
		import from Pair(Ex, Exy), List Pair(Ex, Exy);
		import from Pair(Rax, Raxy), List Pair(Rax, Raxy);
		red := Rax2Ex E;
		A := red a;
		D := red d;
		l := lrt(A, D);
		lif := Ex2Rax E;
		lif2 := Exy2Raxy E;
		ll:List Pair(Rax, Raxy) := empty();
		for pq in l repeat {
			(r, q) := explode pq;
			ll := cons(pair(lif r, lif2 q), ll);
		}
		ir(g, ll);
	}

	-- hermite reduce a/d modulo c, fd is a squarefree factorisation of d
	local hermite(a:Rax, d:Rax, fd:PR, c:COND):Pair(F, F) == {
		import from Product Qax, HermiteIntegration(Qa, Qax);
		import from ParametricUnivariatePolynomialSquareFree(R,var,Rax);
		import from UnivariateFreeAlgebraOverQuotient(Ra, Rax, Qa, Qax);
		zeroCase? c => hermite(simplif(a,c), simplif(d,c), fd, poly c);
		A := makeRational a;
		D := makeRational d;
		FD:Product Qax := 1;
		for term in fd repeat {
			(v, m) := term;
			FD := times!(FD, makeRational v, m);
		}
		(g, h) := hermite(A, D, FD);
		pair(Q2F g, Q2F h);
	}

	local Q2F(f:Q):F == {
		import from Rax;
		import from UnivariateFreeAlgebraOverQuotient(Ra, Rax, Qa, Qax);
		(ca, a) := makeIntegral numerator f;	-- a = ca * numer f
		(cd, d) := makeIntegral denominator f;	-- d = cd * denom f
		-- f = (a/ca)/(d/cd) = cd/ca a/d = (cd a) / (ca d)
		(cd * a) / (ca * d);
	}

	local hermite(a:Rax, d:Rax, fd:PR, p:Ra):Pair(F, F) == {
		macro E == SimpleAlgebraicExtension(R, Ra, p);
		macro Ex == DenseUnivariatePolynomial E;
		import from F, Ex, Product Ex, Quotient Ex;
		import from HermiteIntegration(E, Ex);
		red := Rax2Ex E;
		A := red a;
		D := red d;
		FD:Product Ex := 1;
		for term in fd repeat {
			(v, m) := term;
			FD := times!(FD, red v, m);
		}
		(g, h) := hermite(A, D, FD);
		lif := Ex2Rax E;
		pair(lif(numerator g)/lif(denominator g),
			lif(numerator h)/lif(denominator h));
	}

	local Rax2Ex(K:SimpleAlgebraicExtensionCategory(R,Ra))(p:Rax):DenseUnivariatePolynomial K == {
		import from K;
		q:DenseUnivariatePolynomial K := 0;
		for term in p repeat {
			(c, n) := term;
			q := add!(q, reduce c, n);
		}
		q;
	}

	local Ex2Rax(K:SimpleAlgebraicExtensionCategory(R,Ra))(p:DenseUnivariatePolynomial K):Rax == {
		import from K;
		q:Rax := 0;
		for term in p repeat {
			(c, n) := term;
			q := add!(q, lift c, n);
		}
		q;
	}

	local Exy2Raxy(K:SimpleAlgebraicExtensionCategory(R,Ra))(p:DenseUnivariatePolynomial DenseUnivariatePolynomial K):Raxy == {
		import from K;
		lif := Ex2Rax K;
		q:Raxy := 0;
		for term in p repeat {
			(c, n) := term;
			q := add!(q, lif c, n);
		}
		q;
	}
}
