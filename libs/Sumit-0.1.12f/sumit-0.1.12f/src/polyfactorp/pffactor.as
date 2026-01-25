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
------------------------------ pffactor.as ---------------------------------
-- Copyright (c) Institute of Scientific Computation, ETH Zurich, 1995-1997
-- Copyright INRIA, 1998

#include "sumit"

#if ASDOC
\thistype{PrimeFieldUnivariateFactorizer}
\History{Laurent Bernardin}{8/6/95}{created}
\History{Manuel Bronstein}{27/7/98}{added Shoup's distinct degree factorization}
\Usage{import from \this(F, P)}
\Params{
{\em F} & PrimeFieldCategory0 & Coefficient ring of the polynomials\\
{\em P} & UnivariatePolynomialCategory0 F & A polynomial ring\\
}
\Descr{\this~provides implementations of various univariate factorization
algorithms over a prime field.}
\begin{exports}
berlekamp: & P $\to$ List P & Berlekamp's algorithm\\
cantorZassenhaus: & P $\to$ List P & Cantor-Zassenhaus algorithm\\
factor: & P $\to$ (F, PROD) & Factor using a default algorithm\\
factor: & (P $\to$ List P) $\to$ (P $\to$ (F, PROD)) &
Factor using specified algorithm\\
roots: & P $\to$ List (F,Z) & Roots of a polynomial\\
\end{exports}
\Aswhere{
PROD & == & Product P\\
}
#endif

macro {
	SI == SingleInteger;
	Z  == Integer;
	V  == Vector F;
	M  == DenseMatrix F;
	PL == Product P;
	RR == List Cross(F, Z);
	ARR == PrimitiveArray;
}

PrimeFieldUnivariateFactorizer(F:PrimeFieldCategory0,
				P:UnivariatePolynomialCategory0 F): with {
	berlekamp:		P -> List P;
#if ASDOC
\aspage{berlekamp}
\Usage{\name~p}
\Signature{P}{List P}
\Params{ {\em p} & P & The square free and monic polynomial to factor.\\ }
\Retval{Returns the list of irreducible factors of $p$.}
#endif

	cantorZassenhaus:	P -> List P;
#if ASDOC
\aspage{cantorZassenhaus}
\Usage{\name~p}
\Signature{P}{List P}
\Params{ {\em p} & P & The square free and monic polynomial to factor.\\ }
\Retval{Returns the list of irreducible factors of $p$.}
#endif

	roots:			P -> RR;
#if ASDOC
\aspage{roots}
\Usage{\name~p}
\Signature{P}{List Record(F,Z)}
\Params{{\em p} & P & A polynomial.\\}
\Retval{Returns the roots of $p$ in F with their multiplicities.}
#endif
	rootsSqfr:		P -> List F;
#if ASDOC
\aspage{rootsSqfr}
\Usage{\name~p}
\Signature{P}{List F}
\Params{{\em p} & P & A squarefree polynomial.\\}
\Retval{Returns the roots of $p$ in F, assuming that $p$ is squarefree.}
#endif
	factor:			P -> (F, PL);
	factor:			(P->List P) -> (P->(F, PL));
#if ASDOC
\aspage{factor}
\Usage{\name~p\\ \name(e)(p)}
\Signatures{
\name: & P $\to$ (F, Product P)\\
\name: & (P $\to$ List P) $\to$ (P $\to$ (F, Product P))\\
}
\Params{
{\em p} & P & The polynomial to factor.\\
{\em e} & P $\to$ List P & The factorization engine to use. 
}
\Retval{Returns $(c, p_1^{e_1} \cdots p_n^{e_n})$ such that
each $p_i$ is irreducible, the $p_i$'s have no common factors, and
$$
p = c\;\prod_{i=1}^n p_i^{e_i}\,.
$$
}
\Remarks{Uses the factorizer {\em e} for factoring the monic squarefree
factors of $p$.}
#endif
} == add {
	local charac:Z == characteristic$P;

	-- remove the first occurence of e from l
	local removefromlist(l:List P, e:P):List P == {
		empty? l => l;
		o := first l;
		e = o => rest l;
		cons(o, removefromlist(rest l, e));
	}

	local vector2poly(a:V):P == {
		import from SingleInteger, Z, F;
		m := #a;
		p:P := 0;
		for i in 1..m repeat p := add!(p, a i, (i-1)::Z);
		times!(inv leadingCoefficient p, p);
	}

	berlekamp(a:P):List P == {
		import from Z, F,List V;

		ASSERT(one? leadingCoefficient a);
		ASSERT(one? gcd(a,differentiate a));
		n := (degree a)::SI;
		Q:M := zero(n,n);
		r:M := zero(1,n);
		rn:M := zero(1,n);
		l:M := zero(1,n);
		for i in 1..n repeat l(1,i) := coefficient(a,(i-1)::Z);
		r(1,1) := 1;
		for j in 1..n repeat Q(1,j) := r(1,j);
		for m in charac+1..(n::Z)*charac repeat {
			rn(1,1) := -r(1,n)*l(1,1);
			for j in 2..n repeat {
				rn(1,j) := r(1,j-1) - r(1,n)*l(1,j);
			}
			for j in 1..n repeat r(1,j) := rn(1,j);
			if zero?(m rem charac) then {
				k := m quo charac;
				for j in 1..n repeat Q(k::SI,j) := r(1,j);
			}
		}
		TRACE("Q = ", Q);
		V0 := nullSpace(transpose(Q)+(-one(n)));
		TRACE("V0 = ", V0);
		f:List P := [a];
		rr:SI := 1;
		kk := #V0;
		TRACE("Number of matrix entries = ", kk);
		for i in 1..kk repeat TRACE("", vector2poly V0 i);
		while #f < kk repeat {
			TRACE("poly # ", rr);
			TRACE("poly = ",vector2poly V0 rr);
			ff := copy f;
			while ~empty? ff repeat {
				u := first ff;
				ff := rest ff;
				for i in 0..charac-1 repeat {
					s := i::F;
					TRACE("s = ",s);
					g := gcd(vector2poly(V0 rr) - s::P, u);
					TRACE("gcd = ", g);
					if g ~= 1 and g ~= u and g ~= 0 and
				  	  degree g ~= 0 and
					    degree g ~= degree u then {
						TRACE("found a factor", "");
						uu := u quo g;
						f:=removefromlist(f,u);
						f:=cons(g,f);
						f:=cons(uu,f);
						ff:=cons(g,ff);
						u := uu;
					}
					#f = kk => return f;
				}
			}
			rr := next rr;
			rr > kk => return f;
		}
		f;
	}

	local probsplit(a:P, d:Z):List P == {
		TRACE("pffactor::probsplit, a = ", a);
		TRACE("::d = ", d);
		ASSERT(gcd(a,differentiate a) = 1);
		ASSERT(leadingCoefficient a = 1);
		macro EXT == UnivariatePolynomialMod(F, P, a);
		import from Z, F, EXT;
		dv := degree a;
		ASSERT(zero?(dv rem d));
		r:List P := empty();
		d >= dv => cons(a, r);
		xponent := quotient(charac^d - 1, 2);
		import from SingleInteger;
		count:SingleInteger := 0;
		nterms := max(d, 3);
		repeat {
			t:P := random(2 * d - 1, nterms);
			count := next count;
			TRACE("::count = ", count);
			TRACE("::t = ", t);
			tt := reduce(t)^xponent;
			(t, ap, dummy) := gcdquo(a, lift(tt) - 1);
			dt := degree t;
			if dt ~= 0 and dt ~= dv then {
				l1 := probsplit(t, d);
				l2 := probsplit(ap, d);
				r := concat(l1, l2);
				return r;
			}
		}
	}

	-- look for factors of degree d, d+1, etc.. of v until
	-- either d is greater than deg(v)/2 or a nontrivial factor is found
	-- returns (1 + degree found, poly remaining to factor,
	--          x^(p^degree found), new factors found)
	-- on entry: x = monom, d = degree to look for, v = poly to factor,
	--           w = x^(p^(d-1)) mod v,  f = prod of factors found
	local exhaust!(h:ARR P, store?:Boolean, x:P, d:SI, v:P, bound:SI, w:P,
		f:PL):(SI, P, P, PL) == {
		START__TIME;
		macro EXT == UnivariatePolynomialMod(F, P, v);
		import from Z, EXT, PL;
		ww := reduce w;
		while d <= bound repeat {
			ww := pthPower! ww;		-- ww = x^(p^d)
			TIME("pffactor::exhaust!: p-th power at ");
			w := lift ww;
			if store? then h(next d) := w;
			(g, dummy, newv) := gcdquo(w - x, v);
			TIME("pffactor::exhaust!: gcd(w-x,v) at ");
			degree g > 0 =>	{		-- factors of degree d
				TIME("pffactor::exhaust!: done at ");
				return(next d, newv, remainder!(w, newv),
						times!(f, g, d::Z));
			}
			d := next d;
		}
		TIME("pffactor::exhaust!: done at ");
		(d, v, w, f);
	}

#if SHOUP
	local shoup!(h:ARR P,H:ARR P,j:SI,v:P,f:PL,l:SI,m:SI):(SI,P,PL) == {
		START__TIME;
		macro EXT == UnivariatePolynomialMod(F, P, v);
		import from EXT, PL;
		TRACE("pffactor::shoup!: j = ", j);
		TRACE("pffactor::shoup!: l = ", l);
		TRACE("pffactor::shoup!: m = ", m);
		dv:SI := retract degree v;
		TRACE("pffactor::shoup!: degree of modulus = ", dv);
		w := reduce(H.1);
#if MODCOMP
		comp := compose w;			-- comp(g) = g(x^(p^l))
		TIME("pffactor::shoup!: compose at ");
#endif
		if j > 1 then {
			if j > 2 then w := reduce H(prev j);
#if MODCOMP
			w := comp w;
#else
			for i in 1..l repeat w := pthPower! w;
#endif
			H.j := lift w;
			TIME("pffactor::shoup!: H.j at ");
		}
		found?:Boolean := false;
		cont?:Boolean := (2 * (1 + l * prev j)) <= dv;
		while cont? repeat {
			newv := v;
			for i in 0..prev l repeat {
				lmi := l - i;
				(g, b, newv) := gcdquo(H.j - h.lmi, newv);
				TIME("pffactor::shoup!: gcd at ");
				TRACE("pffactor::shoup!: |gcd| = ",degree g);
				if degree(g) > 0 then {
					found? := true;
					e := l * j - prev lmi;
					f := times!(f, g, e::Z);
				}
			}
			found? => {
				-- reduce powers of x mod new modulus
				for i in 1..l repeat h.i := h.i rem newv;
				for i in 1..j repeat H.i := H.i rem newv;
				TIME("pffactor::shoup!: done at ");
				return(next j, newv, f);
			}
			j := next j;
			TRACE("pffactor::shoup!: j = ", j);
			cont? := (2 * (1 + l * prev j)) <= dv;
			if cont? then {
#if MODCOMP
				w := comp w;
#else
				for i in 1..l repeat w := pthPower! w;
#endif
				H.j := lift w;
				TIME("pffactor::shoup!: H.j at ");
			}
		}
		TIME("pffactor::shoup!: done at ");
		(j, v, f);
	}
#endif

	-- aa is squarefree and monic
	local distdeg(a:P):PL == {
		ASSERT(one? gcd(a, differentiate a));
		ASSERT(one? leadingCoefficient a);
		-- a := copy aa;
		import from SI, Z, F, ARR P;
		w := x := monom;
		f:PL := 1;
		B:SI := retract(degree(a) quo 2);
		d:SI := 1;
#if SHOUP
		import from DoubleFloat, DoubleFloatElementaryFunctions;
		l:SI := retract round sqrt(B::DoubleFloat);
#else
		l:SI := 0;
#endif
		h:ARR P := new next l;		-- h.i will be x^(p^(i-1)) mod a
		h.1 := x;

#if SHOUP
		-- h := pthPowers(x, a, l);	-- h.i = x^(p^(i-1)) mod a
		while d <= min(l, B) repeat {
			(d,a,w,f) := exhaust!(h, true, x, d, a, min(l,B), w, f);
			B := retract(degree(a) quo 2);
		}
		m := B quo l;
		if (m * l) < B then m := next m;
		H:ARR P := new m;
		H.1 := h(next l);		-- x^(p^l) mod a
		j:SI := 1;
		while ((2 * (1 + l * prev j))::Z) <= degree a repeat
			(j, a, f) := shoup!(h, H, j, a, f, l, m);
#else
		while d <= B repeat {
			(d, a, w, f) := exhaust!(h, false, x, d, a, B, w, f);
			B := retract(degree(a) quo 2);
		}
#endif
		one? a => f;
		times!(f, a, degree a);
	}

	cantorZassenhaus(a:P):List P == {
		TRACE("pffactor::cantorZassenhaus: ", a);
		ASSERT(gcd(a,differentiate a) = 1);
		ASSERT(leadingCoefficient a = 1);
		import from F,PL,Z;
		START__TIME;
		f := distdeg a;
		TIME("distinct degree at ");
		TRACE("::disting degree factorization = ", f);
		r:List P := empty();
		for t in f repeat {
			(p,v) := t;
			r := concat(r,probsplit(p,v));
			TIME("probsplit at ");
		}
		TIME("factorisation at ");
		TRACE("pffactor::cantorZassenhaus returns ", r);
		r;
	}

	-- for monic squarefreee polynomials only
	local linearFactors(a:P):List P == {
		ASSERT(one? gcd(a,differentiate a));
		ASSERT(one? leadingCoefficient a);
		import from SI, F, ARR P;
		degree a = 1 => cons(a, empty());
		w := x := monomial(1, 1);
		d:SI := 1;
		f:PL := 1;
		(d, aa, w, f) := exhaust!(new 1, false, x, 1, a, 1, w, f);
		f = 1 => empty(); 
		for t in f repeat (p, dp) := t;
		dp ~= 1 => empty();
		-- TRACE("probsplit of ", p);
		probsplit(p, 1);
	}

	roots(a:P):RR == {
		import from F, List F, RR, Product P;
		lc := leadingCoefficient a;
		aa := inv(lc)*a;
		r:RR := empty();
		(dummy, l) := squareFree aa;
		ASSERT(one? dummy);
		for t in l repeat {
			(p, e) := t;
			if ~zero?(degree p) then
				for rt in rootsSqfrMonic p repeat
					r := cons((rt, e), r);
		}
		r;
	}

	-- for squarefree polynomials only!
	rootsSqfr(a:P):List F == {
		ASSERT(one? gcd(a, differentiate a));
		one?(lc := leadingCoefficient a) => rootsSqfrMonic a;
		rootsSqfrMonic(inv(lc) * a);
	}

	-- for monic squarefree polynomials only!
	local rootsSqfrMonic(a:P):List F == {
		import from List P;
		ASSERT(one? gcd(a, differentiate a));
		ASSERT(one? leadingCoefficient a);
		r:List(F) := empty();
		for f in linearFactors a repeat {
			ASSERT(one? leadingCoefficient f);
			r := cons(- coefficient(f, 0), r);
		}
		r;
	}

	factor(a:P):(F, PL) == factor(cantorZassenhaus)(a);

	factor(engine:P->List P)(a:P):(F, PL) == {
		import from F,List P,List Cross(P,Z),Product P;
		-- TRACE("factor ", a);
		lc := leadingCoefficient a;
		aa := inv(lc)*a;
		(dummy,l) := squareFree aa;
		-- TRACE("squarefree factorization = ", l);
		-- TRACE("lcoeff = ", dummy);
		ASSERT(dummy=1);
		r:PL := 1;
		for t in l repeat {
			(p,e) := t;
			if zero? degree p then {
				lc := lc * (leadingCoefficient p)^e;
				iterate;
			}
			l1 := engine p;
			while ~empty? l1 repeat {
				f := first l1;
				l1 := rest l1;
				if f~=1 then r:=times!(r,f,e);
			}
		}
		-- TRACE("factor:returning lc = ", lc);
		-- TRACE("and ", r);
		(lc,r);
	}				
}
