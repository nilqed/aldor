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
------------------------------- zfactor.as --------------------------------
#include "sumit"

#if ASDOC
\thistype{UnivariateIntegralFactorizer}
\History{Laurent Bernardin}{4/12/95}{created}
\History{Manuel Bronstein}{22/07/98}
{factortryprime: added combinations of factors}
\Usage{import from \this(Z, P);}
\Params{
{\em Z} & IntegerCategory & An integer-like ring\\
{\em P} & UnivariatePolynomialCategory0 Z & A polynomial type over Z\\
}
\Descr{\this(Z, P) implements a factorizer for polynomials with
integer coefficients.}
\begin{exports}
factor: & P $\to$ Record(lcoeff:Z,factors:Product P) & Factor\\
integerRoots: & P $\to$ List RationalRoot & Integer roots\\
rationalRoots: & P $\to$ List RationalRoot & Rational roots\\
\end{exports}
#endif

macro {
	I	== SingleInteger;
	PZ	== DenseUnivariatePolynomial Z;
	RR	== RationalRoot;
}

UnivariateIntegralFactorizer(Z:IntegerCategory,
			P:UnivariatePolynomialCategory0 Z): with {
	factor:			P	->	(Z, Product P);
#if ASDOC
\aspage{factor}
\Usage{\name~p}
\Signature{P}{(Z,Product P)}
\Params{ {\em p} & P & A polynomial with integer coefficients\\ }
\Retval{Returns $(c, p_1^{e_1} \cdots p_n^{e_n})$ such that
each $p_i$ is irreducible, the $p_i$'s have no common factors, and
$$
p = c\;\prod_{i=1}^n p_i^{e_i}\,.
$$
}
\seealso{squareFree(UnivariatePolynomialCategory0)}
#endif
	integerRoots:		P	->	List RR;
#if ASDOC
\aspage{integerRoots}
\Usage{\name~p}
\Signature{P}{List RationalRoot}
\Params{ {\em p} & P & A polynomial with integer coefficients\\ }
\Retval{Return $[(r_1,e_1),\dots,(r_n,e_n)]$ where the $r_i$'s are
the integer roots of $p$ and have multiplicity $e_i$.}
#endif
	rationalRoots:		P	->	List RR;
#if ASDOC
\aspage{rationalRoots}
\Usage{\name~p}
\Signature{P}{List RationalRoot}
\Params{ {\em p} & P & A polynomial with integer coefficients\\ }
\Retval{Return $[(r_1,e_1),\dots,(r_n,e_n)]$ where the $r_i$'s are
the rational roots of $p$ and have multiplicity $e_i$.}
#endif
} == add {
	local maxHeightLinearFactor(f:P):Z == {
		import from Integer;
		zero? f => 0;
		b:Z := 0;
		i:Integer := 0;
		while zero? b repeat {
			b := coefficient(f, i);
			i := next i;
		}
		b < 0 => -b;
		b;
	}

	local maxHeightFactor(f:P):Z == (degree f)*2^(degree f)*height(f);

	integerRoots(f:P):List RR == {
		import from Product P, Integer, RR, Z, List Cross(Z,Z);
		TRACE("zfactor::integerRoots: ", f);
		r:List RR := empty();
		(lc, s) := squareFree f;
		for t in s repeat {
			(p, e) := t;
			for rr in findroots(p, false) repeat {
				(N, D) := rr;
				if one? D then
					r := cons(integerRoot(integer N,
								integer e), r);
			}
		}
		TRACE("zfactor::integerRoots returns ", r);
		r;
	}

	factor(f:P):(Z, Product P) == {
		import from Integer,List P;
		r:Product P := 1;
		u := leadingCoefficient f;
		if u>0 then u := 1;
		else {
			f := -f;
			u := -1;
		}
		(lc,s) := squareFree f;
		for t in s repeat {
			(p, e) := t;
			fr := findfactors p;
			for rr in fr repeat r := times!(r, rr, e);
		}
		(u * lc, r);
	}

	local ratrecon(u:Z,m:Z,nb:Z,db:Z):Partial Cross(Z,Z) == {
		(s0,t0):Z := (0,1);
		(s1,t1):Z := (m,u rem m);
		while nb<abs(t1) repeat {
			(q,r1) := divide(s1,t1);
			r0 := s0-q*t0;
			(s0,s1) := (t0,t1);
			(t0,t1) := (r0,r1);
		}
		abs(t0)>db => failed;
		[(t1,t0)];
	}

	rationalRoots(f:P):List RR == {
		import from Product P,Integer, Z, List Cross(Z,Z);
		r:List RR := empty();
		(lc, s) := squareFree f;
		for t in s repeat {
			(g, e) := t;
			for rr in findroots(g, true) repeat {
				(N, D) := rr;
				r := cons(rationalRoot(integer N, integer D,
							integer e), r);
			}
		}
		r;
	}

	-- f must be squarefree
	local findroots(f:P, dorational:Boolean):List Cross(Z,Z) == {
		import from I, Z, SmallPrimes;
		zero?(d := degree f) => empty();
		d = 1 => {
			import from Integer, Partial Z;
			u:=exactQuotient(coefficient(f,0),leadingCoefficient f);
			failed? u => empty();
			cons((- retract u,1),empty());
		}
		bound := maxHeightLinearFactor(f) + 1;
		TRACE("zfactor::findroots, f = ",f);
		p:I := 5;
		unlucky?:Boolean := true;
		while unlucky? repeat {
			(r, unlucky?) := roottryprime(f, p, bound, dorational);
			p := nextPrime p;
		}
		TRACE("zfactor::findroots returns ",r);
		r;
	}

	local findfactors(f:P):List P == {
		import from SmallPrimes, Integer, Z;
		(d := degree f) <= 1 => [f];
		bound := maxHeightFactor(f) + 1;
		TRACE("zfactor::findfactors: f = ",f);
		TRACE("zfactor::findfactors: bound = ",bound);
		p:I := 5;
		(r,f) := factortryprime(f,p,bound);
		while f~=1 repeat {
			TRACE("::looking for factors of: ",f);
			p := nextPrime(p);
			(r1,f) := factortryprime(f,p,bound);
			r := concat(r,r1);
			TRACE("::now got these factors: ",r);
		}
		TRACE("zfactor::findfactors returns = ",r);
		r;
	}

	local factortryprime(f:P,p:I,bound:Z):(List P, P) == {
		macro {
			F == ZechPrimeField p;
			PF == DenseUnivariatePolynomial F;
		}
		import from Integer, F, PF, Product PF;
		import from UnivariateHenselLifting(Z,P,F,PF);
		import from Partial P,Partial List P;

		TRACE("zfactor::factortryprime, f = ", f);
		TRACE("::prime = ", p);
		fp := downgrade f;
		if degree fp ~= degree f then {
			TRACE("::unlucky prime"," returning empty");
			return (empty(),f);
		}
		(mfcoeff, mfc):=factor fp;
		-- ASSERT(mfcoeff=1);
		mf:List PF := empty();
		nfacts:I := 0;
		for tt in mfc repeat {
			(pp,e) := tt;
			if e~=1 then {
				TRACE("::evaluation not square free",
					 " returning empty");
				return (empty(),f);
			}
			mf := cons(pp,mf);
			nfacts := next nfacts;
		}
		nfacts=1 => (cons(f,empty()),1);
		TRACE("::Number of modular factors: ",nfacts);
		liftbound := 2@Z * abs(leadingCoefficient f) * bound;
		TRACE("::liftbound = ",liftbound);
		TRACE("::Modular factors = ", mf);
		(lf,pk) := linearLift(f, mf, liftbound);
		TRACE("::lifting failed = ", failed? lf);
		failed? lf => (empty(),f);
		pkfactors := retract lf;
		TRACE("zfactor::factortryprime:lifted factors: ", pkfactors);
		TRACE("zfactor::factortryprime:modulo: ", pk);
		i:I := 1;
		tf:List P := empty();
		while i <= (#pkfactors) quo 2 repeat {
			(tf0,pkfactors,f):= tryCombinations(pkfactors,f,i,1,pk);
			tf := concat!(tf, tf0);
			i := next i;
		}
		TRACE("zfactor::factortryprime:returns ", cons(f, tf));
		(cons(f,tf), 1); 
	}

	-- returns a mod p in [-p/2,+p/2]
	local balred(a:Z, p:Z):Z == {
		ASSERT(odd? p);
		p2 := p quo 2;
		b := a rem p;
		b > p2 => b - p;
		b;
	}

	-- computes pq mod modulus, balanced representation
	local times(p:P, q:P, modulus:Z):P == {
		pq := p * q;
		ans:P := 0;
		for term in pq repeat {
			(c, e) := term;
			ans := add!(ans, balred(c, modulus), e);
		}
		ans;
	}

	local tryCombinations(l:List P,f:P,i:I,prod:P,pk:Z):(List P,List P,P)=={
		import from Partial P;
		i = 0 => {
			q := exactQuotient(f, prod);
			failed? q => (empty(), l, f);
			([prod], l, retract q);
		}
		i > #l => (empty(), l, f);
		l1 := first l;
		-- l will be the candidates left minus l1
		-- if tf is empty, then l1 must be added back as a candidate
		(tf,l,f):=tryCombinations(rest l,f,prev i,times(prod,l1,pk),pk);
		~empty?(tf) and ~one?(prod) => (tf, l, f);
		(tff, l, f) := tryCombinations(l, f, i, prod, pk);
		empty? tf => (tff, cons(l1, l), f);
		(concat!(tf, tff), l, f);
	}

	-- second argument is true when the prime p was unlucky
	local roottryprime(f:P,p:I,bound:Z,
			dorational:Boolean):(List Cross(Z, Z), Boolean) == {
		macro {
			F == ZechPrimeField p;
			PF == DenseUnivariatePolynomial F;
		}
		import from Integer, F, PF, UnivariateHenselLifting(Z,P,F,PF);
		import from List F, Partial Z, Partial P;
		import from Partial Cross(Z, Z);

		TRACE("zfactor::roottryprime, f = ", p);
		TRACE(":: prime = ", p);
		fp := downgrade f;
		degree(fp) ~= degree(f) or zero?(g := gcd(fp, differentiate fp))
			or degree(g) > 0 => {
				TRACE("::unlucky prime"," returning empty");
				(empty(), true);
		}
		irl := rootsSqfr(PF)(fp);
		TRACE("::done computing modular roots","");
		r:List Cross(Z, Z) := empty();
		empty? irl => return (r, false); 
		TRACE("::Number of modular roots: ", #irl);
		DB := abs(leadingCoefficient f);
		liftbound := 2@Z * DB * bound;
		for ir in irl repeat {
			TRACE("::lifting root: ",ir);
			(rr,liftk) := linearLift(f, ir, liftbound);
			if ~failed? rr then {
				TRACE("::lifted root: ",retract rr);
				q := exactQuotient(f, monomial(1, 1) -
							monomial(retract rr,0));
				if ~failed? q then {
					TRACE("::found root ",retract rr);
					f := retract q; 
					r := cons((retract rr,1), r);
				}
				else if dorational then {
					NB := liftk quo ((2@Z)*DB);
					if (2@Z)*DB*NB = liftk then
						NB := NB-1;
					rrr := retract rr;
					qq := ratrecon(rrr,liftk,NB,DB);
					if ~failed? qq then {
						(n,d) := retract qq;
						q := exactQuotient(f,
								d*monomial(1,1)-
								monomial(n,0));
						if ~failed? q then {
							f := retract q;
							r := cons((n,d),
								r);
						}
					}
				}
			}
		}
		TRACE("zfactor::roottryprime, returns ", r);
		(r, false);
	}
}			

#if SUMITTEST
---------------------- test zfactor.as --------------------------
#include "sumittest"

macro {
	Z == Integer;
	Q == Quotient Z;
	P == DenseUnivariatePolynomial(Z, "x");
	RR == RationalRoot;
}

integerRoots():Boolean == {
	import from Z, P, RR, List RR;
	x == monom;
	f := x^5 + 8120 * x^4 - 6299183 * x^3 - 9446096526 * x^2 +
					3671637382172 * x + 51412443096::P;
	l := integerRoots f;
	mult:Z := 1;
	count:Z := 0;
	t1234:Boolean := false; tm987:Boolean := false; t346:Boolean := false;
	for rt in l repeat {
		~integer? rt => return false;
		n := integerValue rt;
		mult := mult * multiplicity(rt);
		count := next count;
		if n = 1234 then t1234 := true;
		else if n = 346 then t346 := true;
		else if n = -987 then tm987 := true;
	}
	count = 3 and mult = 1 and t1234 and t346 and tm987;
}

rationalRoots():Boolean == {
	import from Z, Q, P, RR, List RR;
	x := monom;
	f := 13*x^9+384*x^8-1485*x^7+13*x^3+397*x^2-1101*x-1485::P;
	l := rationalRoots f;
	mult:Z := 1;
	count:Z := 0;
	tm33:Boolean := false; t4513:Boolean := false;
	for rt in l repeat {
		(n, d) := value rt;
		q := n / d;
		mult := mult * multiplicity(rt);
		count := next count;
		if q = -33::Q then tm33 := true;
		else if q = 45/13 then t4513 := true;
	}
	count = 2 and mult = 1 and tm33 and t4513;
}

factor():Boolean == {
	import from Z, P, Product P;
	x == monom;
	f := 20*x^5-96*x^4+1191439*x^3-6889560*x^2-21718242087*x+17378393004::P;
	(lcoeff, p) := factor f;
	count:Z := 0;
	for term in p repeat count := count + 1;
	lcoeff = 1 and count = 4 and expand p = f;
}

print << "Testing zfactor..." << newline;
sumitTest("integerRoots", integerRoots);
sumitTest("rationalRoots", rationalRoots);
sumitTest("factor", factor);
print << newline;
#endif

