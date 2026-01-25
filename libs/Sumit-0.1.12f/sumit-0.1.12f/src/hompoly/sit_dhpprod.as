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
---------------------------- sit_dhpprod.as ------------------------------
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I	== MachineInteger;
	Z	== Integer;
	TREE	== ExpressionTree;
	ARR	== PrimitiveArray;
}

#if ALDOC
\thistype{DenseHomogeneousPowerProduct}
\History{Manuel Bronstein}{18/12/95}{created}
\Usage{ import from \this(n, m)\\ }
\Params{
{\em n} & \astype{MachineInteger} & The total degree\\
{\em m} & \astype{MachineInteger} & The number of variables\\
}
\Descr{\this(n, m) implements dense homogeneous power products
of total degree $n$ in $m$ variables, \ie~products of the form
$$
\prod_{i=1}^m X_i^{e_i}\quad\mbox{where}\quad\sum_{i=1}^m e_i = n\,.
$$
}
\begin{exports}
\category{\astype{FiniteSet}}\\
\asexp{degree}: & (\%, I) $\to$ I &
Degree in a variable\\
\asexp{eval}:
& (S:\astype{Ring}, \astype{Array} S) $\to$ \% $\to$ S & Evaluation\\
\asexp{incdec}: & (\%, I, I) $\to$ \% & Increment/Decrement exponents\\
\asexp{monomial}: & I $\to$ \% & Create a monomial $X_i^n$\\
\asexp{multinomial}: & \% $\to$ I & Multinomial of a multiexponent\\
\asexp{weight}: & \% $\to$ I & Weight\\
\end{exports}
\begin{aswhere}
I &==& \astype{MachineInteger}\\
\end{aswhere}
#endif

DenseHomogeneousPowerProduct(n:I, m:I):FiniteSet with {
	degree: (%, I) -> I;
#if ALDOC
\aspage{degree}
\Usage{ \name(p, i) }
\Signature{(\%, \astype{MachineInteger})}{\astype{MachineInteger}}
\Params{
{\em p} & \% & A power product\\
{\em i} & \astype{MachineInteger} & The index of a variable\\
}
\Retval{Returns the exponent of $X_i$ in $p$.}
#endif
	eval: (S:Ring, Array S) -> % -> S;
#if ALDOC
\aspage{eval}
\Usage{\name(S, $[a_1,\dots,a_m]$)(p)}
\Signature{(S:\astype{Ring}, \astype{Array} S)}{\% $\to$ S}
\Params{
{\em S} & \astype{Ring} & A ring\\
{\em $a_i$} & S & A value for $X_i$\\
{\em p} & \% & A power product\\
}
\Retval{Returns $\prod_{i=1}^m a_i^{e_i}$ where $p = \prod_{i=1}^m X_i^{e_i}$.}
#endif
	incdec: (%, I, I) -> %;
#if ALDOC
\aspage{incdec}
\Usage{ \name(p, i, j) }
\Signature{(\%, \astype{MachineInteger}, \astype{MachineInteger})}{\%}
\Params{
{\em p} & \% & A power product\\
{\em i,j} & \astype{MachineInteger} & Indices of variables\\
}
\Retval{Returns $p X_i X_j^{-1}$.}
\Remarks{The exponent of $X_j$ in $p$ must be greater than $0$.}
#endif
	monomial: I -> %;
#if ALDOC
\aspage{monomial}
\Usage{ \name~i}
\Signature{\astype{MachineInteger}}{\%}
\Params{ {\em i} & \astype{MachineInteger} & The index of a variable\\ }
\Retval{Returns the power product $X_i^n$.}
#endif
	multinomial: % -> Z;
#if ALDOC
\aspage{multinomial}
\Usage{\name~p}
\Signature{\%}{\astype{Integer}}
\Params{ {\em p} & \% & A power product\\ }
\Retval{Returns
$$
\frac{n!}{e_1! \cdots e_m!}
$$
where
$$
p = \prod_{i=1}^m X_i^{e_i} \quad\mbox{ and }\quad \sum_{i=1}^m e_i = n
$$
}
#endif
	weight: % -> I;
#if ALDOC
\aspage{weight}
\Usage{\name~p}
\Signature{\%}{\astype{MachineInteger}}
\Params{ {\em p} & \% & A power product\\ }
\Retval{Returns
$$
\sum_{i=1}^m (i-1) e_i
$$
where
$$
p = \prod_{i=1}^m X_i^{e_i}
$$
}
#endif
} == add {
	Rep == ARR I;	-- the exponents from 1 to m

	import from I, Rep;

	#:Z		== binomial(prev(m::Z + n::Z), prev(m::Z));
	local size:I	== machine(#$%);
	local nfact:Z	== factorial(n::Z);
 
	eval(S:Ring, a:Array S):% -> S == {
		import from I, S, Z, Bits;
		assert(m <= #a);
		zer? := false m;
		for ai in a for i in 1@I.. repeat zer?.i := zero? ai;
		(p:%):S +-> {
			s:S := 1;
			for ai in a for i in 1@I.. | (d := degree(p, i)) > 0
				repeat {
					zer?.i => return 0;
					s := s * ai^(d::Z);
				}
			s;
		}
	}

	multinomial(p:%):Z == {
		d:Z := 1;
		for i in 1..m repeat d := d * factorial(degree(p, i)::Z);
		quotient(nfact, d);
	}

	apply(p:%, x:TREE):TREE == {
		import from Boolean, String, List TREE;
		l:List TREE := empty;
		for i in 1..m | ~zero?(d := degree(p, i)) repeat
			l := cons(extree(d, x, i), l);
		assert(~empty? l);
		empty? rest l => first l;
		ExpressionTreeTimes reverse! l;
	}

	local extree(d:I, x:TREE, n:I):TREE == {
		import from List TREE;
		e := ExpressionTreeSubscript [x, extree n];	-- x_n
		assert(d > 0);
		d = 1 => e;
		ExpressionTreeExpt [e, extree d];
	}

	(a:%) = (b:%):Boolean == {
		for i in 1..m repeat degree(a,i) ~= degree(b,i) => return false;
		true;
	}

	local copyrep(a:%):Rep == {
		b:Rep := new m;
		for i in 0..prev m repeat b.i := rep(a).i;
		b;
	}

	-- this ordering causes X1^n < X1^(n-1) X2 < ... < Xm^n
	(a:%) < (b:%):Boolean == {
		for i in 1..m repeat {
			(da := degree(a, i)) ~= (db := degree(b, i)) =>
				return(da > db);
		}
		false;
	}

	lookup(j:Z):% == {
		import from ARR %;
		assert(j >= 1); assert(j <= #$%);
		basis(machine prev j);
	}

	-- enumerates all the homogeneous monomials of total degree deg
	-- in vars variables, store them in a(frum), a(frum+1), etc...
	-- use prefix to create the monomial, it contains the exponents
	-- of the previous variables
	-- returns the next free index in a
	local enumerate(a:ARR %, frum:I, deg:I, vars:I, prefix:%):I == {
		p := copyrep prefix;
		zero? deg => {
			a.frum := per p;
			next frum;
		}
		vars = 1 => {
			p(prev m) := deg;
			a.frum := per p;
			next frum;
		}
		for i in 0..deg repeat {
			p.(m - vars) := i;
			frum := enumerate(a, frum, deg - i, prev vars, per p);
		}
		frum;
	}

	local reverse!(a:ARR %, frum:I, two:I):ARR % == {
		while frum < two repeat {
			x := a.frum;
			a.frum := a.two;
			a.two := x;
			frum := next frum;
			two := prev two;
		}
		a;
	}

	-- computes the basis with lex ordering X1 < X2 < ... < Xm
	basis:ARR % == {
		enumerate(a := new size, 0, n, m, per new(m, 0));
		reverse!(a, 0, prev size);
	} where { a:ARR % }

	-- relies on the fact that basis is sorted ascending
	index(p:%):Z == {
		import from ARR %, BinarySearch(I, %);
		(found?, i) := binarySearch(p, (j:I):% +-> basis.j,0,prev size);
		assert found?;
		next(i::Z);
	}

	degree(p:%, i:I):I == {
		assert(i > 0); assert(i <= m);
		rep(p)(prev i);
	}

	monomial(i:I):% == {
		assert(i > 0); assert(i <= m);
		a := new(m, 0);
		a(prev i) := n;
		per a;
	}

	incdec(p:%, i:I, j:I):% == {
		assert(i > 0); assert(i <= m);
		assert(j > 0); assert(j <= m);
		assert(degree(p, j) > 0);
		a := copyrep p;
		i := prev i; j := prev j;
		a.i := next(a.i);
		a.j := prev(a.j);
		per a;
	}

	weight(p:%):I == {
		w:I := 0;
		for j in 1..m repeat w := w + prev(j) * degree(p, j);
		w;
	}
}
