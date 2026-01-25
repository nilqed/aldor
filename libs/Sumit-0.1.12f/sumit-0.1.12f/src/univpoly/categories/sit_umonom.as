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
----------------------------- sit_umonom.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------


#include "sumit"

#if ALDOC
\thistype{UnivariateMonomial}
\History{Manuel Bronstein}{20/5/94}{created}
\Usage{import from \this~R\\ import from \this(R, x)}
\Params{
{\em R} & \astype{SumitType} & Coefficients of the monomials\\
        & \astype{ArithmeticType} &\\
{\em x} & \astype{Symbol} & The variable name (optional)\\
}
\Descr{This type implements univariate monomials with coefficients in R.}
\begin{exports}
%\category{\astype{Order}}\\
\category{\astype{SumitType}}\\
\asexp{apply}: & (\%, TREE) $\to$ TREE & Applies a monomial to a tree\\
\asexp{coefficient}: & \% $\to$ R & Extraction of the coefficient\\
\asexp{degree}: & \% $\to$ \astype{Integer} & The degree of a monomial\\
\asexp{map}: & (R $\to$ R) $\to$ \% $\to$ \% & Lift a map\\
\asexp{map!}: & (R $\to$ R) $\to$ \% $\to$ \% & Lift a map\\
\asexp{monomial}: & (R, \astype{Integer}) $\to$ \% & Creation of a monomial\\
\asexp{setCoefficient!}:
& (\%, R) $\to$ R & In--place coefficient modification\\
\asexp{setDegree!}: & (\%, Z) $\to$ Z & In-place degree modification\\
\end{exports}
\begin{exports}[if $R$ has \astype{FiniteCharacteristic} then]
\asexp{pthPower}: & \% $\to$ \% & Exponentiation to the characteristic\\
\asexp{pthPower!}:
& \% $\to$ \% & In--place exponentiation to the characteristic\\
\end{exports}
\begin{aswhere}
TREE &==& \astype{ExpressionTree}\\
\end{aswhere}
#endif

macro {
	Z == Integer;
	TREE == ExpressionTree;
}

UnivariateMonomial(R:Join(ArithmeticType, SumitType), var:Symbol == new()):
	SumitType with {
	apply: (%, TREE) -> TREE;
#if ALDOC
\aspage{apply}
\Usage{\name(p, t)}
\Signature{(\%, \astype{ExpressionTree})}{\astype{ExpressionTree}}
\Params{
{\em p} & \% & A monomial\\
{\em t} & \astype{ExpressionTree} & An expression tree\\
}
\Retval{Returns p as an expression tree using t as root variable name.}
#endif
	coefficient: % -> R;
#if ALDOC
\aspage{coefficient}
\Usage{\name~p}
\Signature{\%}{R}
\Params{ {\em p} & \% & A monomial\\ }
\Retval{Returns the coefficient of $p$, \ie $c$ where $p = c\; x^n$.}
\seealso{\asexp{degree}, \asexp{setCoefficient!}}
#endif
	degree: % -> Z;
#if ALDOC
\aspage{degree}
\Usage{\name~p}
\Signature{\%}{\astype{Integer}}
\Params{ {\em p} & \% & A monomial\\ }
\Retval{Returns the degree of $p$, \ie $n$ where $p = c\; x^n$.}
\seealso{\asexp{coefficient}}
#endif
	map: (R -> R) -> % -> %;
	map!: (R -> R) -> % -> %;
#if ALDOC
\aspage{map}
\astarget{\name!}
\Usage{\name~f\\\name!~f\\\name(f)(p)\\\name!(f)(p)}
\Signature{(R $\to$ R) $\to$ \%}{\%}
\Params{
{\em f} & R $\to$ R & A map\\
{\em p} & \% & A monomial\\
}
\Descr{\name(f)(p) returns $f(a) x^n$ where $p = a x^n$,
while \name(f) returns the mapping $p \to f(p)$.
In both cases, \name!~does not make a copy of $p$ but modifies it in place.}
#endif
	monomial: (R, Z) -> %;
#if ALDOC
\aspage{monomial}
\Usage{\name(c, n)}
\Signature{(R, \astype{Integer})}{\%}
\Params{
{\em c} & R & A scalar\\
{\em n} & \astype{Integer} & An exponent\\
}
\Retval{Returns the monomial $c\; x^n$.}
#endif
	if R has FiniteCharacteristic then {
        	pthPower: % -> %;
        	pthPower!: % -> %;
#if ALDOC
\aspage{pthPower}
\astarget{\name!}
\Usage{ \name~p\\ \name!~p }
\Signature{\%}{\%}
\Params{ {\em p} & \% & A monomial\\ }
\Retval{Returns $p^{\mbox{characteristic}}$.}
\Remarks{\name!~does not make a copy of $p$, which is therefore
modified after the call. It is unsafe to use the variable $p$
after the call, unless it has been assigned to the result
of the call, as in {\tt p := pthPower!~p}.}
#endif
	}
	setCoefficient!: (%, R) -> R;
#if ALDOC
\aspage{setCoefficient!}
\Usage{\name(p, c)}
\Signature{(\%, R)}{R}
\Params{
{\em p} & \% & A monomial\\
{\em c} & R & A scalar\\
}
\Descr{Sets the coefficient of $p$ to $c$,\ie changes $p = d\; x^n$ into
$c\; x^n$}
\Retval{Returns the new coefficient $c$.}
\seealso{\asexp{coefficient}}
#endif
	setDegree!: (%, Z) -> Z;
#if ALDOC
\aspage{setDegree!}
\Usage{\name(p, c)}
\Signature{(\%, \astype{Integer})}{\astype{Integer}}
\Params{
{\em p} & \% & A monomial\\
{\em n} & \astype{Integer} & An exponent\\
}
\Descr{Sets the degree of $p$ to $n$,\ie changes $p = c\; x^m$ into
$c\; x^n$}
\Retval{Returns the new degree $n$.}
\seealso{\asexp{degree}}
#endif
} == add {
	Rep == Record(coef:R, expt:Z);
	import from Rep;

	local evar:TREE				== extree var;
	monomial(c:R, n:Z):%			== { assert(n>=0); per [c, n]; }
	coefficient(t:%):R     			== rep(t).coef;
	degree(t:%):Z    	  		== rep(t).expt;
	setDegree!(t:%, n:Z):Z			== rep(t).expt := n;
	setCoefficient!(t:%, c:R):R		== rep(t).coef := c;
	extree(p:%):TREE			== p evar;
	map(f:R -> R)(p:%):%	== monomial(f coefficient p, degree p);
	map!(f:R -> R)(p:%):%	== { setCoefficient!(p, f coefficient p); p }

	apply(p:%, t:TREE):TREE == {
		import from R, List TREE;
		zero?(c := coefficient p) => extree c;
		d := degree p;
		negative?(tc := extree c) =>
			ExpressionTreeMinus [tree(c ~= -1, negate tc, d, t)];
		tree(c ~= 1, tc, d, t);
	}

	local tree(tims?:Boolean, c:TREE, n:Z, t:TREE):TREE == {
		import from R, List TREE;
		zero? n => c;
		if n > 1 then t := ExpressionTreeExpt [t, extree n];
		tims? => ExpressionTreeTimes [c, t];
		t;
	}

	(u:%) = (v:%):Boolean == {
		degree u = degree v and coefficient u = coefficient v;
	}

	if R has FiniteCharacteristic then {
		pthPower(p:%):% ==
			monomial(pthPower(coefficient p)$R,
					characteristic$R * degree p);

		pthPower!(p:%):% == {
			rec := rep p;
			rec.coef := pthPower(rec.coef)$R;
			rec.expt := characteristic$R * rec.expt;
			p;
		}
	}
}

#if SUMITTEST
---------------------- test umonom.as --------------------------
#include "sumittest"

macro {
        Z == Integer;
	F == SmallPrimeField 11;
        M == UnivariateMonomial;
}

double(a:Z):Z == a + a;

degree():Boolean == {
        import from Z, M Z;
        p := monomial(2, 3);
	q := map(double)(p);
        degree p = 3 and coefficient p = 2 and
		degree q = degree p and coefficient q = 4;
}

pthpower():Boolean == {
        import from MachineInteger, Z, F, M F;

        p := monomial(2, 3);
	q := pthPower p;
	degree p = 3 and coefficient p = 2 and
		degree q = characteristic$F * degree p
			and coefficient q = coefficient p;
}

stdout << "Testing umonom..." << endnl;
sumitTest("degree", degree);
sumitTest("pthpower", pthpower);
stdout << endnl;
#endif

