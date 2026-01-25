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
------------------------------ rateval.as ------------------------------
#include "sumit"
#include "uid"

macro {
	Symbol == String;
	Z  == Integer;
	Zx == Quotient ZX;
}

#if ASDOC
\thistype{RationalFunctionEvaluator}
\History{Manuel Bronstein}{15/04/98}{created}
\Usage{import from \this~ZX}
\Params{ ZX & UnivariatePolynomialCategory Integer & a polynomial type\\ }
\Descr{\this~ZX provides an interpreter that converts expression trees
to the fraction field of ZX, or to linear structures over it.}
\begin{exports}
eval: & (TREE, String) $\to$ Partial Zx & Interpret a fraction\\
evalArray: & (TREE, String) $\to$ Partial Array Zx &
Interpret an array of fractions\\
evalList: & (TREE, String) $\to$ Partial List Zx &
Interpret a list of fractions\\
evalMatrix: & (TREE, String) $\to$ Partial DenseMatrix Zx &
Interpret a matrix of fractions\\
\end{exports}
\begin{aswhere}
TREE &==& ExpressionTree\\
Zx &==& Quotient ZX\\
\end{aswhere}
#endif

RationalFunctionEvaluator(ZX:UnivariatePolynomialCategory Z): with {
	eval: (ExpressionTree, s:Symbol == "") -> Partial Zx;
#if ASDOC
\aspage{eval}
\Usage{\name~t\\ \name(t, s)\\}
\Signature{(ExpressionTree, .:String == "")}{Partial Quotient ZX}
\Params{
t & ExpressionTree & An expression tree\\
s & String & A variable name (optional)\\
}
\Retval{Returns the fraction represented by t, if t represents a fraction,
\failed~otherwise.}
\Remarks{The optional parameter s is the name of the polynomial
variable name in the tree t. If it is not present, then the name of the
polynomial variable in ZX is used instead.}
\seealso{evalArray(\this)\\ evalList(\this)}
#endif
	evalArray: (ExpressionTree, s:Symbol == "") -> Partial Array Zx;
#if ASDOC
\aspage{evalArray}
\Usage{\name~t\\ \name(t, s)\\}
\Signature{(ExpressionTree, .:String == "")}{Partial Array Quotient ZX}
\Params{
t & ExpressionTree & An expression tree\\
s & String & A variable name (optional)\\
}
\Retval{Returns the array of fractions represented by t,
if t represents such an array or list, \failed~otherwise.}
\Remarks{The optional parameter s is the name of the polynomial
variable name in the tree t. If it is not present, then the name of the
polynomial variable in ZX is used instead.}
\seealso{eval(\this)\\ evalList(\this)\\ evalMatrix(\this)}
#endif
	evalList: (ExpressionTree, s:Symbol == "") -> Partial List Zx;
#if ASDOC
\aspage{evalList}
\Usage{\name~t\\ \name(t, s)\\}
\Signature{(ExpressionTree, .:String == "")}{Partial List Quotient ZX}
\Params{
t & ExpressionTree & An expression tree\\
s & String & A variable name (optional)\\
}
\Retval{Returns the list of fractions represented by t,
if t represents such a list or array, \failed~otherwise.}
\Remarks{The optional parameter s is the name of the polynomial
variable name in the tree t. If it is not present, then the name of the
polynomial variable in ZX is used instead.}
\seealso{evalArray(\this)\\ eval(\this)\\ evalMatrix(\this)}
#endif
	evalMatrix: (ExpressionTree, s:Symbol == "") -> Partial DenseMatrix Zx;
#if ASDOC
\aspage{evalMatrix}
\Usage{\name~t\\ \name(t, s)\\}
\Signature{(ExpressionTree, .:String == "")}{Partial DenseMatrix Quotient ZX}
\Params{
t & ExpressionTree & An expression tree\\
s & String & A variable name (optional)\\
}
\Retval{Returns the matrix of fractions represented by t,
if t represents such an matrix given by a list of lists or array of arrays,
\failed~otherwise.}
\Remarks{The optional parameter s is the name of the polynomial
variable name in the tree t. If it is not present, then the name of the
polynomial variable in ZX is used instead.}
\seealso{eval(\this)\\ evalArray(\this)\\ evalList(\this)}
#endif
} == add {
	local integer(a:Zx):Partial Z == {
		import from Z, ZX;
		one? denominator a and zero? degree(n := numerator a) =>
							[leadingCoefficient n];
		failed;
	}

	local UnivariateRationalFunction(ZX:UnivariatePolynomialCategory Z):
		PartialRing with {
			coerce: Zx -> %;
			coerce: % -> Zx;
	} == MakePartialRing(Zx, integer);

	macro R == UnivariateRationalFunction ZX;

	local RationalEvaluator(ZX:UnivariatePolynomialCategory Z):Evaluator R
		== add {};

	eval(tree:ExpressionTree, s:Symbol):Partial Zx == eval0(tree, symbol s);

	local symbol(s:Symbol):Symbol == {
		import from ZX, ExpressionTree, ExpressionTreeLeaf;
		s = "" and leaf?(x := extree monom) and symbol?(l := leaf x) =>
			symbol l;
		s;
	}

	local eval0(tree:ExpressionTree, s:Symbol):Partial Zx == {
		import from ZX, Zx, R, Partial R, SymbolTable R;
		import from RationalEvaluator ZX;
		TRACE("rateval::eval0, tree = ", tree);
		t := table();
		t.s := monom::Zx::R;
		failed?(u := eval!(print, tree, t)) => failed;
		[retract(u)::Zx];
	}

	local linear?(tree:ExpressionTree):Boolean ==
		(~leaf? tree) and linear0? tree;

	local linear0?(tree:ExpressionTree):Boolean == {
		import from SingleInteger;
		ASSERT(~leaf? tree);
		op := uniqueId$operator(tree);
		(op = UID__LIST) or (op = UID__LLIST) or (op = UID__VECTOR);
	}

	evalMatrix(tree:ExpressionTree, s:Symbol):Partial DenseMatrix Zx == {
		import from SingleInteger, Zx, Partial Zx, DenseMatrix Zx;
		import from List ExpressionTree;
		~linear? tree => failed;
		s := symbol s;
		zero?(r := #(args := arguments tree)) => [zero(0,0)];
		leaf?(row := first args) => failed;
		c := #(arguments row);
		m:DenseMatrix Zx := zero(r, c);
		for i in 1..r for arg in args repeat {
			argsi := arguments arg;
			(~linear? arg) or (c ~= #argsi) => return failed;
			for j in 1..c for col in argsi repeat {
				failed?(u := eval0(col, s)) => return failed;
				m(i, j) := retract u;
			}
		}
		[m];
	}

	evalArray(tree:ExpressionTree, s:Symbol):Partial Array Zx == {
		import from SingleInteger, Zx, Partial Zx, Array Zx;
		import from List ExpressionTree;
		~linear? tree => failed;
		s := symbol s;
		n := #(args := arguments tree);
		a:Array Zx := new(n, 0);
		for i in 1..n for arg in args repeat {
			failed?(u := eval0(arg, s)) => return failed;
			a.i := retract u;
		}
		[a];
	}

	evalList(tree:ExpressionTree, s:Symbol):Partial List Zx == {
		import from Partial Zx, List Zx, List ExpressionTree;
		~linear? tree => failed;
		s := symbol s;
		l:List Zx := empty();
		for arg in arguments tree repeat {
			failed?(u := eval0(arg, s)) => return failed;
			l := cons(retract u, l);
		}
		[reverse! l];
	}
}
