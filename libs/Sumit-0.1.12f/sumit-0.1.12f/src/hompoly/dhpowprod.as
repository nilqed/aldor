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
------------------------------ dhpowprod.as ------------------------------
#include "sumit"

#if ASDOC
\thistype{DenseHomogeneousPowerProduct}
\History{Manuel Bronstein}{18/12/95}{created}
\Usage{ import from \this(n, m)\\ }
\Params{
{\em n} & SingleInteger & The total degree\\
{\em m} & SingleInteger & The number of variables\\
}
\Descr{\this(n, m) implements dense homogeneous power products
of total degree $n$ in $m$ variables, \ie~products of the form
$$
\prod_{i=1}^m X_i^{e_i}\quad\mbox{where}\quad\sum_{i=1}^m e_i = n\,.
$$
}
\begin{exports}
\category{FiniteSet}\\
degree: & (\%, SingleInteger) $\to$ I & Degree in a variable\\
eval: & (S:Ring, Array S) $\to$ \% $\to$ S & Evaluation\\
incdec: & (\%, SingleInteger, SingleInteger) $\to$ \% &
Increment/Decrement exponents\\
monomial: & SingleInteger $\to$ \% & Create a monomial $X_i^n$\\
multinomial: & \% $\to$ Integer & Multinomial of a multiexponent\\
weight: & \% $\to$ SingleInteger & Weight\\
\end{exports}
#endif

macro {
	I	== SingleInteger;
	Z	== Integer;
	TREE	== ExpressionTree;
	Symbol	== String;
}

DenseHomogeneousPowerProduct(n:I, m:I):FiniteSet with {
	degree: (%, I) -> I;
#if ASDOC
\aspage{degree}
\Usage{ \name(p, i) }
\Signature{(\%, SingleInteger)}{SingleInteger}
\Params{
{\em p} & \% & A power product\\
{\em i} & SingleInteger & The index of a variable\\
}
\Retval{Returns the exponent of $X_i$ in $p$.}
#endif
	eval: (S:Ring, Array S) -> % -> S;
#if ASDOC
\aspage{eval}
\Usage{\name(S, $[a_1,\dots,a_m]$)(p)}
\Signature{(S:Ring, Array S)}{\% $\to$ S}
\Params{
{\em S} & Ring & A ring\\
{\em $a_i$} & S & A value for $X_i$\\
{\em p} & \% & A power product\\
}
\Retval{Returns $\prod_{i=1}^m a_i^{e_i}$ where $p = \prod_{i=1}^m X_i^{e_i}$.}
#endif
	incdec: (%, I, I) -> %;
#if ASDOC
\aspage{incdec}
\Usage{ \name(p, i, j) }
\Signature{(\%, SingleInteger, SingleInteger)}{\%}
\Params{
{\em p} & \% & A power product\\
{\em i,j} & SingleInteger & Indices of variables\\
}
\Retval{Returns $p X_i X_j^{-1}$.}
\Remarks{The exponent of $X_j$ in $p$ must be greater than $0$.}
#endif
	monomial: I -> %;
#if ASDOC
\aspage{monomial}
\Usage{ \name~i}
\Signature{SingleInteger}{\%}
\Params{ {\em i} & SingleInteger & The index of a variable\\ }
\Retval{Returns the power product $X_i^n$.}
#endif
	multinomial: % -> Z;
#if ASDOC
\aspage{multinomial}
\Usage{\name~p}
\Signature{\%}{Integer}
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
#if ASDOC
\aspage{weight}
\Usage{\name~p}
\Signature{\%}{SingleInteger}
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
	macro Rep == PrimitiveArray I;	-- the exponents from 1 to m

	import from I, Rep;

	-- inefficient for now
	local binomial(a:I, b:I):Z == {
		import from Z, Partial Z;
		A := a::Z; B := b::Z;
		retract exactQuotient(factorial A,
					factorial(B) * factorial(A - B));
	}

	sample:%		== monomial 1;
	#:Z			== binomial(m + n - 1, m - 1);
	local size:I		== retract(#$%);
	local nfact:Z		== factorial(n::Z);
 
	eval(S:Ring, a:Array S):% -> S == {
		import from I, Z, PrimitiveArray Boolean;
		assert(m <= #a);
		zer?:PrimitiveArray Boolean := new m;
		for i in 1..m repeat zer?.i := zero?(a.i);
		(p:%):S +-> {
			s:S := 1;
			for i in 1..m | (d := degree(p, i)) > 0 repeat {
				zer?.i => return 0;
				s := s * a.i^(d::Z);
			}
			s;
		}
	}

	multinomial(p:%):Z == {
		d:Z := 1;
		for i in 1..m repeat d := d * factorial(degree(p, i)::Z);
		quotient(nfact, d);
	}

	apply(p:%, x:Symbol):TREE == {
		import from List TREE;
		l:List TREE := empty();
		for i in 1..m | ~zero?(d := degree(p, i)) repeat
			l := cons(extree(d, extree(x, i)), l);
		assert(~empty? l);
		empty? rest l => first l;
		ExpressionTreeTimes reverse! l;
	}

	local extree(x:Symbol, i:I):TREE == {
		import from Format;
		format(i, s := "__abcdefghij", 2);
		extreeSymbol concat(x, s);
	}

	local extree(d:I, x:TREE):TREE == {
		import from List TREE;
		assert(d > 0);
		d = 1 => x;
		ExpressionTreeExpt [x, extree d];
	}

	(a:%) = (b:%):Boolean == {
		for i in 1..m repeat degree(a,i) ~= degree(b,i) => return false;
		true;
	}

	local copy(a:Rep):Rep == {
		b:Rep := new m;
		for i in 1..m repeat b.i := a.i;
		b;
	}

	-- this ordering causes X1^n < X1^(n-1) X2 < ... < Xm^n
	(a:%) > (b:%):Boolean == {
		for i in 1..m repeat {
			(da := degree(a, i)) ~= (db := degree(b, i)) =>
				return(da < db);
		}
		false;
	}

	lookup(j:I):% == {
		assert(j <= size);
		import from PrimitiveArray %;
		basis.j;
	}

	-- enumerates all the homogeneous monomials of total degree deg
	-- in vars variables, store them in a(frum), a(frum+1), etc...
	-- use prefix to create the monomial, it contains the exponents
	-- of the previous variables
	-- returns the next free index in a
	local enumerate(a:PrimitiveArray %,frum:I,deg:I,vars:I,prefix:Rep):I=={
		p := copy prefix;
		zero? deg => {
			a.frum := per p;
			next frum;
		}
		vars = 1 => {
			p.m := deg;
			a.frum := per p;
			next frum;
		}
		for i in 0..deg repeat {
			p.(m + 1 - vars) := i;
			frum := enumerate(a, frum, deg - i, prev vars, p);
		}
		frum;
	}

	local reverse!(a:PrimitiveArray %, frum:I, two:I):PrimitiveArray % == {
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
	basis:PrimitiveArray % == {
		enumerate(a := new size, 1, n, m, new(m, 0));
		reverse!(a, 1, size);
	} where { a:PrimitiveArray % }

	-- relies on the fact that basis is sorted ascending
	index(p:%):I == {
		import from PrimitiveArray %, BinarySearch(I, %);
		(found?, i) := binarySearch(p, (j:I):% +-> basis.j, 1, size);
		assert found?;
		i;
	}

	degree(p:%, i:I):I == {
		assert(i > 0); assert(i <= m);
		rep(p).i;
	}

	monomial(i:I):% == {
		assert(i > 0); assert(i <= m);
		a := new(m, 0);
		a.i := n;
		per a;
	}

	incdec(p:%, i:I, j:I):% == {
		assert(i > 0); assert(i <= m);
		assert(j > 0); assert(j <= m);
		assert(degree(p, j) > 0);
		a := copy rep p;
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
