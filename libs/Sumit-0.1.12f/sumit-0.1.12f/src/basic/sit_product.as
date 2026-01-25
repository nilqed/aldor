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
------------------------------- sit_product.as -------------------------------
--
-- Formal products, used for example for factorisation results
--
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{Product}
\History{Manuel Bronstein}{6/6/95}{created}
\Usage{import from \this~R}
\Params{ {\em R} & \astype{CommutativeRing} & A commutative ring\\ }
\Descr{\this~R provides finite products of elements of R,~\ie elements
of the type $\prod_{i=1}^n r_i^{e_i}$ where the $r_i$'s are in R and the
$e_i$'s are integers.}
\begin{exports}
\category{\astype{CopyableType}}\\
\category{\astype{Monoid}}\\
\asexp{\#}: & \% $\to$ \astype{MachineInteger} & Number of terms\\
\asexp{divisors}:
& \% $\to$ \astype{Generator} R & Iterate through all the divisors\\
\asexp{expand}: & \% $\to$ R & Multiply-out a product\\
\asexp{generator}:
& \% $\to$ \astype{Generator} \builtin{Cross}(R, \astype{Integer}) &
Make an iterator\\
\asexp{term}: & (R, \astype{Integer}) $\to$ \% & Create a single term $r^e$\\
\asexp{times!}: & (\%, R, \astype{Integer}) $\to$ \% & In-place multiplication\\
\end{exports}
#endif

macro {
	A	== PrimitiveArray;
	Z	== Integer;
}

Product(R:CommutativeRing): Join(CopyableType, Monoid) with {
	#: % -> MachineInteger;
#if ALDOC
\aspage{\#}
\Usage{\name~p}
\Signature{\%}{\astype{MachineInteger}}
\Params{ {\em p} & \% & A product\\ }
\Retval{Returns the number of terms in the product p.}
#endif
	divisors: % -> Generator %;
#if ALDOC
\aspage{divisors}
\Usage{ for d in \name~p repeat \{ \dots \} }
\Signature{\%}{\astype{Generator} R}
\Params{ {\em p} & \% & A product\\ }
\Descr{This generator yields all the products of the form
$\prod_{i=1}^n r_i^{f_i}$ where $p = \prod_{i=1}^n r_i^{e_i}$
and $0 \le f_i \le e_i$.}
\begin{asex}
\begin{ttyout}
import from Integer, Product Integer, List Integer;

p := term(3, 1) * term(2, 2) * term(5, 2)       -- p = 3^1 2^2 5^2 = 300
l := sort! [divisors p];
\end{ttyout}
creates the list
\begin{asoutput}
\> [1,2,3,4,5,6,10,12,15,20,25,30,50,60,75,100,150,300]\\
\end{asoutput}
of all the divisors of $300$.
\end{asex}
#endif
	expand: % -> R;
#if ALDOC
\aspage{expand}
\Usage{\name~p}
\Signature{\%}{R}
\Params{ {\em p} & \% & A product\\ }
\Retval{Returns the product of all the terms in p.}
#endif
	generator: % -> Generator Cross(R, Z);
#if ALDOC
\aspage{generator}
\Usage{
for term in p repeat \{ (c, n) := term; \dots \}\\
for term in \name~p repeat \{ (c, n) := term; \dots \}
}
\Signature{\%}{\astype{Generator} \builtin{Cross}(R, \astype{Integer})}
\Params{ {\em p} & \% & A product\\ }
\Descr{This function allows a product to be iterated independently of its
representation. The generator yields pairs of the form $(a, n)$ where
$a^n$ is a term in $p$.}
\begin{asex}
\begin{ttyout}
import from Integer, Product Integer;

p := term(3, 1) * term(2, 11) * term(5, 2)       -- p = 3^1 2^11 5^2
for term in p repeat { (c, n) := term; stdout << c << "," << n << newline; }
\end{ttyout}
writes
\begin{asoutput}
\> 3,1\\
\> 2,11\\
\> 5,2
\end{asoutput}
to the standard stream \asfunc{TextWriter}{stdout}.
\end{asex}
#endif
	term: (R, Z) -> %;
#if ALDOC
\aspage{term}
\Usage{\name(r, n)}
\Signature{(R, \astype{Integer})}{\%}
\Params{
{\em r} & R & A ring element\\
{\em n} & \astype{Integer} & An exponent\\
}
\Retval{Returns $r^e$ as a product.}
#endif
	times!: (%, R, Z) -> %;
#if ALDOC
\aspage{times!}
\Usage{\name(p, r, n)}
\Signature{(\%, R, \astype{Integer})}{\%}
\Params{
{\em p} & \% & A product\\
{\em r} & R & A ring element\\
{\em n} & \astype{Integer} & An exponent\\
}
\Retval{Returns $p\; r^e$ as a product, where the storage used by p is allowed
to be destroyed or reused, so p is lost after this call.}
\Remarks{The storage used by p is allowed to be destroyed or reused, so p
is lost after this call. This may cause p to be destroyed, so do not use
this unless p has been locally allocated, and is thus guaranteed not
to share space with other polynomials. Some functions are not necessarily
copying their arguments and can thus create memory aliases.}
#endif
} == add {
	-- TEMPORARY: workaround to bug 1187
	local TERM: PrimitiveType with {
		maketerm: (R, Z) -> %;
		exponent: % -> Z;
		coefficient: % -> R;
	} == add {
		macro Rep == Record(trm:R, exp:Z);

		maketerm(x:R, n:Z):%	== { import from Rep; per [x, n] }
		exponent(t:%):Z		== { import from Rep; rep(t).exp }
		coefficient(t:%):R	== { import from Rep; rep(t).trm }

		(a:%) = (b:%):Boolean == {
			import from R, Z;
			exponent a = exponent b
				and coefficient a = coefficient b;
		}
	}

	macro {
		-- TEMPORARY: workaround to bug 1187
		-- TERM	== Record(trm:R, exp:Z);
		Rep	== List TERM;
	}

	import from TERM, Rep;

	1:%				== per empty;
	-- TEMPORARY: workaround to bug 1187
	-- local exponent(term:TERM):Z	== term.exp;
	-- local coefficient(term:TERM):R	== term.trm;
	#(p:%):MachineInteger		== # rep p;
	copy(p:%):%			== per copy rep p;
	divisors(x:%):Generator %	== div rep x;

	term(x:R, n:Z):% == {
		zero? n or one? x => 1;
		-- TEMPORARY: workaround to bug 1187
		-- per [[x, n]];
		per [maketerm(x, n)];
	}

	generator(x:%):Generator Cross(R, Z) == generate {
		for t in rep x repeat yield(coefficient t, exponent t);
	}

	local div(l:Rep):Generator % == generate {
		import from Z;
		if empty? l then yield 1;
		else {
			t := first l;
			c := coefficient t;
			n := exponent t;
			for d in div rest l repeat
				for i in 0..n repeat yield(term(c, i) * d);
		}
	}

	(x:%) ^ (m:Z):% == {
		import from R;
		y:% := 1;
		zero? m => y;
		for t in x repeat {
			(c, n) := t;
			if one? c then y := times!(y, c, n);
				else y := times!(y, c, m * n);
		}
		y;
	}

	-- very naive for now, no simplification whatsoever
	(a:%) * (b:%):% == {
		one? a => b; one? b => a;
		p := copy b;
		for t in a repeat {
			(c, n) := t;
			p := times!(p, c, n);
		}
		p;
	}

	times!(p:%, x:R, n:Z):% == {
		zero? n or one? x => p;
		per cons(first rep term(x, n), rep p);
	}

	-- very inneficient for now
	(a:%) = (b:%):Boolean == { import from R; expand(a) = expand(b); }

	expand(x:%):R == {
		a:R := 1;
		for t in x repeat {
			(c, n) := t;
			a := times!(a, c^n);
		}
		a;
	}

	extree(x:%):ExpressionTree == {
		import from R, List ExpressionTree;
		l := [term2tree(coefficient t, exponent t) for t in rep x];
		empty? l => extree(1$R);
		empty? rest l => first l;
		ExpressionTreeTimes l;
	}

	local term2tree(g:R, c:Z):ExpressionTree == {
		import from List ExpressionTree;
		assert(c ~= 0);
		tg := extree g;
		one? c => tg;
		tc := extree c;
		ExpressionTreeExpt [tg, tc];
	}
}
