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
------------------------------ dhextprod.as ------------------------------
#include "sumit"

#if ASDOC
\thistype{DenseHomogeneousExteriorProduct}
\History{Manuel Bronstein}{17/2/97}{created}
\Usage{ import from \this(n, m)\\ }
\Params{
{\em n} & SingleInteger & The total degree\\
{\em m} & SingleInteger & The number of variables\\
}
\Descr{\this(n, m) implements dense homogeneous exterior products
of total degree $n$ in $m$ variables, \ie~exterior products of the form
$$
X_{e_1} \wedge X_{e_2} \wedge\dots \wedge X_{e_n}
\quad\mbox{where}\quad 1 \le e_1 < e_2 < \dots < e_n \le m\,.
$$
}
\begin{exports}
\category{FiniteSet}\\
appears?: & (\%, I) $\to$ Boolean & Degree in a variable\\
increment: & (\%, I) $\to$ Partial \% & Increment variable\\
principalProduct: & $\to$ \% & $X_1 \wedge \dots \wedge X_n$\\
replace: & (\%, I, I) $\to$ (I, \%) &
Replace variable\\
\end{exports}
\begin{aswhere}
I &==& SingleInteger\\
\end{aswhere}
#endif

macro {
	I	== SingleInteger;
	TREE	== ExpressionTree;
	Symbol	== String;
}

DenseHomogeneousExteriorProduct(n:I, m:I):FiniteSet with {
	appears?: (%, I) -> Boolean;
#if ASDOC
\aspage{appears?}
\Usage{ \name(p, i) }
\Signature{(\%, SingleInteger)}{Boolean}
\Params{
{\em p} & \% & An exterior product\\
{\em i} & SingleInteger & The index of a variable\\
}
\Retval{Returns \true~if $X_i$ appears in $p$, \false~otherwise.}
#endif
	increment: (%, I) -> Partial %;
#if ASDOC
\aspage{increment}
\Usage{ \name(p, i) }
\Signature{(\%, SingleInteger)}{Partial \%}
\Params{
{\em p} & \% & An exterior product\\
{\em i} & SingleInteger & A position\\
}
\Descr{$\name(X_{e_1} \wedge \dots \wedge X_{e_n}, i)$ returns
$X_{e_1}\wedge\dots\wedge
X_{e_{i-1}}\wedge X_{e_i+1}\wedge X_{e_{i+1}}\wedge\dots X_{e_n}$
if either $e_i + 1 < e_{i+1}$ or $i = n$ and $e_n < m$, \failed~otherwise.}
#endif
	principalProduct: %;
#if ASDOC
\aspage{principalProduct}
\Usage{\name}
\Signature{}{\%}
\Retval{Returns $X_1\wedge \dots \wedge X_n$.}
#endif
	replace: (%, I, I) -> (I, %);
#if ASDOC
\aspage{replace}
\Usage{ (s, q) := \name(p, i, j) }
\Signature{(\%, SingleInteger, SingleInteger)}{(SingleInteger, \%)}
\Params{
{\em p} & \% & An exterior product\\
{\em i,j} & SingleInteger & Indices\\
}
\Descr{$\name(X_{e_1} \wedge \dots \wedge X_{e_n}, i, j)$ returns
$(\epsilon, X_{f_1} \wedge \dots \wedge X_{f_n})$ where
$1 \le f_1 < f_2 < \dots < f_n \le m$ and
$\{f_1,\dots,f_n\} = \{e_1,\dots,e_n,j\}\setminus\{i\}$
if $\epsilon\ne 0$. In that case $\epsilon = \pm 1$ is the sign
of the permutation needed to get from $(e_1,\dots,e_n)$
with $i$ replaced by $j$ to $(f_1,\dots,f_n)$.}
#endif
} == add {
	macro Rep == I;	 -- bit bi set means X_{e_{i+1}} is in the product

	import from Rep;

	-- inefficient for now
	local binomial(a:I, b:I):Integer == {
		import from Integer, Partial Integer;
		A := a::Integer; B := b::Integer;
		retract exactQuotient(factorial A,
					factorial(B) * factorial(A - B));
	}

	principalProduct:%	== per prev shift(1, n);	-- 2^n - 1
	sample:%		== principalProduct;
	#:Integer		== binomial(m, n);
	local size:I		== retract(#$%);
	(a:%) = (b:%):Boolean	== rep(a) = rep(b);
	(a:%) > (b:%):Boolean	== rep(a) > rep(b);
	local xi(i:I):I		== shift(1, prev i);		-- X_i

	apply(p:%, x:Symbol):TREE == {
		import from List TREE;
		l:List TREE := empty();
		for i in 1..m | appears?(p,i) repeat l := cons(extree(x,i),l);
		ASSERT(~empty? l);
		empty? rest l => first l;
		ExpressionTreeTimes reverse! l;
	}

	local extree(x:Symbol, i:I):TREE == {
		import from Format;
		format(i, s := "__abcdefghij", 2);
		extreeSymbol concat(x, s);
	}

	lookup(j:I):% == {
		ASSERT(j <= size);
		import from PrimitiveArray %;
		basis.j;
	}

	-- enumerates all the homogeneous exterior products of total degree deg
	-- in vars variables, store them in a(frum), a(frum+1), etc...
	-- returns the next free index in a
	local enumerate(a:PrimitiveArray %, frum:I, deg:I, vars:I):I == {
		ASSERT(deg > 0); ASSERT(deg <= vars);
		deg = vars => {
			a.frum := per prev shift(1, vars);	-- 2^vars - 1
			next frum;
		}
		-- generate all prods of degree deg among X_1,...,X_{vars - 1}
		frum := enumerate(a, frum, deg, prev vars);
		mask := xi vars;				-- X_vars
		deg = 1 => {
			a.frum := per mask;
			next frum;
		}
		-- generate all prods of degree deg-1 among X_1,...,X_{vars-1}
		done := enumerate(a, frum, prev deg, prev vars);
		-- add X_vars to those products
		for i in frum..prev done repeat a.i := per(rep(a.i) \/ mask);
		done;
	}

	basis:PrimitiveArray % == {
		enumerate(a := new size, 1, n, m);
		a;
	} where { a:PrimitiveArray % }

	index(p:%):I == {
		import from PrimitiveArray %, BinarySearch(I, %);
		(found?, i) := binarySearch(p, (j:I):% +-> basis.j, 1, size);
		ASSERT found?;
		i;
	}

	appears?(p:%, i:I):Boolean == {
		ASSERT(i > 0); ASSERT(i <= m);
		bit(rep p, prev i);
	}

	-- returns the index of the i-th set bit of a (starts at 0)
	local ithbit(a:I, i:I):I == {
		ASSERT(i > 0); ASSERT(i <= n);
		ones:I := 0;
		j:I := -1;
		while ones < i repeat {
			j := next j;
			if bit(a, j) then ones := next ones;
		}
		j;
	}

	replace(p:%, i:I, j:I):(I, %) == {
		ASSERT(i > 0); ASSERT(i <= m);
		ASSERT(j > 0); ASSERT(j <= m);
		ASSERT(appears?(p, i));
		i = j => (1, p);
		b:I := shift(1, prev i);
		c:I := shift(1, prev j);
		appears?(p, j) => (0, p);
		a := rep p;
		(signature(a, prev i, prev j), per((a /\ ~b) \/ c));
	}

	-- returns (-1)^#{bits of a which are set and strictly between i and j}
	local signature(a:I, i:I, j:I):I == {
		i > j => signature(a, j, i);
		s:I := 1;
		k := next i;
		while k < j repeat {
			if bit(a, k) then s := -s;
			k := next k;
		}
		s;
	}

	increment(p:%, i:I):Partial % == {
		ASSERT(i > 0); ASSERT(i <= n);
		j := ithbit(a := rep p, i);
		j = prev m or bit(a, next j) => failed;
		b:I := shift(1, j);
		[per((a /\ ~b) \/ shift(b, 1))];
	}
}
