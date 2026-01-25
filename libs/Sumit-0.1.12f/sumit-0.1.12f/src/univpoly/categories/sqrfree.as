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
------------------------------  sqrfree.as ---------------------------------
#include "sumit"

#if ASDOC
\thistype{UnivariatePolynomialSquareFree}
\History{Laurent Bernardin}{24/5/95}{created}
\Usage{import from \this(R, P)}
\Params{
{\em R} & GcdDomain & Coefficient ring of the polynomials\\
{\em P} & UnivariatePolynomialCategory0 R & A polynomial ring\\
}
\Descr{\this~provides implementations of various squarefree factorization
algorithms.}
\begin{exports}
musser: & P $\to$ (R, Product P) & Musser's algorithm\\
yun: & P $\to$ (R, Product P) & Yun's algorithm\\
\end{exports}
#endif

macro {
	Z	== Integer;
	PR	== Product P;
}

UnivariatePolynomialSquareFree(R:GcdDomain,
	P:UnivariatePolynomialCategory0 R): with {
		musser:	P -> (R, PR);
#if ASDOC
\aspage{musser}
\Usage{\name~p}
\Signature{P}{(R, Product P)}
\Params{ {\em p} & P & The polynomial to factor\\ }
\Retval{Returns $(c, p_1^{e_1} \cdots p_n^{e_n})$ such that
each $p_i$ is squarefree, the $p_i$'s have no common factors, and
$$
p = c\;\prod_{i=1}^n p_i^{e_i}\,.
$$
}
\seealso{yun(\this)}
#endif
		yun:	P -> (R, PR);
#if ASDOC
\aspage{yun}
\Usage{\name~p}
\Signature{P}{(R, Product P)}
\Params{ {\em p} & P & The polynomial to factor\\ }
\Retval{Returns $(c, p_1^{e_1} \cdots p_n^{e_n})$ such that
each $p_i$ is squarefree, the $p_i$'s have no common factors, and
$$
p = c\;\prod_{i=1}^n p_i^{e_i}\,.
$$
}
\seealso{musser(\this)}
#endif
} == add { 
	local charac:Z		== characteristic$P;
	local charp?:Boolean	== R has FiniteCharacteristic;
	local field?:Boolean	== R has Field;
	local finite?:Boolean	== R has Finite;

	if R has FiniteField then {
		local exponentReduction(a:P):P == {
			r:P := 0;
			for term in a repeat {
				(c, n) := term;
				ASSERT(zero?(n rem charac));
				r := add!(r, c, quotient(n, charac));
			}
			r;
		}
	
		local charpMusser(a:P):PR == {
			import from R;
			ASSERT(a ~= 0);
			ASSERT(one? leadingCoefficient a);
			zero? degree a => 1;
			zero?(ap := differentiate a) => {
				aa := exponentReduction a;
				(charpMusser aa)^charac;
			}
			(g, astar, dummy) := gcdquo(a, ap);
			zero? degree g => term(a, 1);
			(gstar, d1, dummy) := gcdquo(astar, g);
			a := quotient(a, d1);
			r := term(d1, 1);
			for term in charpMusser g repeat {
				(q, e) := term;
				if zero?(e rem charac) then {
					r := times!(r, q, e);
					a := quotient(a, q^e);
				}
				else {
					r := times!(r, q, next e);
					a := quotient(a, q^(next e));
				}
			}
			zero? degree a => r;
			rr:PR := 1;
			for term in r repeat {
				(q, e) := term;
				if zero?(e rem charac) then {
					(g, a, q) := gcdquo(a, q);
					rr := times!(times!(rr,g,next e), q, e);
				}
				else rr := times!(rr, q, e);
			}
			rr;
		}

		local charpYun(a:P):PR == {
			ASSERT(a ~= 0);
			b := differentiate a;
			(c, w, v) := gcdquo(a, b);
			zero? degree c => term(a, 1);
			u := v - differentiate w;
			r:PR := 1;
			i:Z := 1;
			while (i < charac - 1) and (u ~= 0) repeat {
				(g, w, v) := gcdquo(w, u);
				if degree g > 0 then r := times!(r, g, i);
				c := c quo w;
				u := v - differentiate w;
				i := next i;
			}
			if degree w > 0 then r := times!(r, w, i);
			zero? degree c => r;
			k:Z := 1;
			c := exponentReduction c;
			while degree c > 0 and zero? differentiate c repeat {
				c := exponentReduction c;
				k := next k;
			}
			h := charpYun c;
			rnew:PR := 1;
			rleft:PR := 1;
			for t1 in r repeat {
				(p1, e1) := t1;
				if p1 = 1 then iterate;
				hh := h;
				h:PR := 1;
				for t2 in hh repeat {
					(p2,e2) := t2;
					if p2 = 1 then iterate;
					(g, p1, p2) := gcdquo(p1, p2);
					if degree g > 0 then {
						rnew := times!(rnew, g,
								e2*charac^k+e1);
					}
					h := times!(h, p2, e2);
				}
				rleft := times!(rleft, p1, e1);
			}
			rnew := rleft * rnew;
			for t1 in h repeat {
				(p1,e1) := t1;
				rnew := times!(rnew, p1, e1*charac^k);
			}
			r := 1;
			for t1 in rnew repeat {
				(p1,e1) := t1;
				if p1~=1 then r := times!(r, p1, e1);
			}
			r; 	
		}	
	}

	else {
		local char0Musser(a:P, n:Z):PR == {
			import from Partial P;
			ASSERT(a ~= 0);
			(g, astar, dummy) := gcdquo(a, differentiate a);
			zero? degree g => term(a, n);
			(gstar, d1, dummy) := gcdquo(astar, g);
			times!(char0Musser(g, next n), d1, n);
		}

		local char0Yun(a:P):PR == {
			ASSERT(a ~= 0);
			i:Z := 1;
			r:PR := 1;
			b := differentiate a;
			(c,w,y) := gcdquo(a,b);	-- c = gcd(a,b)= a/w = b/y
			if c~=1 then {
				z := y - differentiate w;
				while z~=0 repeat {
					(g,w,y) := gcdquo(w,z);
					if degree(g)>0 then r:=times!(r,g,i);
					i := next i;
					z := y - differentiate w;
				}
			}
			times!(r,w,i);
		}
				
	}

	local normalize(a:P):(R, P) == {
		ASSERT(a ~= 0);
		field? => fieldNormal a;
		primitive a;
	}

	if R has Field then {
		local fieldNormal(a:P):(R,P) == (leadingCoefficient a, monic a);
	}

	yun(a:P):(R, PR) == {
		zero? a => (0, 1);
		(c, a) := normalize a;
		charp? => { ASSERT finite?; (c, charpYun a); }
		(c, char0Yun a);
	}

	musser(a:P):(R, PR) == {
		zero? a => (0, 1);
		(c, a) := normalize a;
		charp? => (c, charpMusser a);
		(c, char0Musser(a,1));
	}
}

#if SUMITTEST
------------------------ test sqrfree.as ---------------------
#include "sumittest.as"

macro {
	Z == Integer;
	Zx == SparseUnivariatePolynomial(Z, "x");
	F == ZechPrimeField 5;
	Fx == SparseUnivariatePolynomial(F, "x");
}

import from SingleInteger;

local char0(f:Zx -> (Z, Product Zx)):Boolean == {
	import from Z, Zx, PrimitiveArray Z, Product Zx;
	x := monom;
	p:Zx := 1;
	for i in 1..5@Z repeat p := p * (x - i::Zx)^i;
	(c, pr) := f p;
	hit := new(5@SingleInteger, 0);
	i:Z := 0;
	(degree p ~= 15) or (c ~= 1) or ((c * expand pr) ~= p) => false;
	for term in pr repeat {
		(q, n) := term;
		degree(q) ~= 1 => return false;
		hit(retract n) := 1;
		i := next i;
	}
	for j in 1..5@SingleInteger repeat { zero?(hit.j) => return false; }
	i = 5;
}

local char0():Boolean == {
	import from UnivariatePolynomialSquareFree(Z, Zx);
	char0(musser) and char0(yun);
}

local charp(f:Fx -> (F, Product Fx)):Boolean == {
	import from Z, F, Fx, PrimitiveArray Z, Product Fx;
	x := monom;
	p:Fx := (3@Z)*1;
	for i in 1..4@Z repeat p := p * (x^2 + i*1)^i;
	for i in 1..3@Z repeat p := p * (x^2 + x + i*1)^(i+4);
	p := p * (x^2 + (3@Z)*x + (4@Z)*1)^8;
	for i in 1..4@Z repeat p := p * (x + i*1)^(i+8);
	(c, pr) := f p;
	c ~= 3 => false;
	(c ~= 3) or ((c * expand pr) ~= p) => false;
	hit := new(23@SingleInteger,0);
	for term in pr repeat {
		(q,n) := term;
		(n>8) and degree(q)~=1 => return false;
		(n<=8) and degree(q)~=2 => return false;
		n>23 => return false;
		hit(n::SingleInteger):=1;
	}
	hit(2):=hit(2)-1;
	hit(3):=hit(3)-1;
	hit(5):=hit(5)-1;
	hit(6):=hit(6)-1;
	hit(8):=hit(8)-1;
	hit(12):=hit(12)-1;
	hit(13):=hit(13)-1;
	hit(18):=hit(18)-1;
	hit(23):=hit(23)-1;
	for j in 1..23@SingleInteger repeat {
		if hit(j)~=0 then return false;
	}
	true;
}

local charp():Boolean == {
	import from UnivariatePolynomialSquareFree(F, Fx);
	charp(musser) and charp(yun);
}
	
print << "Testing sqrfree..." << newline;
sumitTest("Characteristic zero", char0);
sumitTest("Characteristic p", charp);
print << newline;
#endif
