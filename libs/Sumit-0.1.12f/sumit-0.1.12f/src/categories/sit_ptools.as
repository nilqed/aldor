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
----------------------------- sit_ptools.as ----------------------------------
--
-- This file provides help-functions for parsing expression trees
--
-- This type must be included inside "sit_pable.as" to be compiled,
-- but is in a separate file for documentation purposes.
--
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#if ALDOC
\thistype{ParsingTools}
\History{Manuel Bronstein}{30/08/99}{created}
\Usage{import from \this~R}
\Params{
{\em R} & \astype{Parsable} & A parsable arithmetic system\\
        & \astype{ArithmeticType} &\\
}
\Descr{\this~R provides tools for converting
expression trees into elements of R.}
\begin{exports}
\asexp{evalArith}: & \astype{ExpressionTreeLeaf} $\to$ \builtin{Partial} R &
Interpret an arbitrary leaf\\
\asexp{evalInt}:
& \astype{ExpressionTree} $\to$ \builtin{Partial} \astype{Integer} &
Interpret an integer\\
\end{exports}
#endif

ParsingTools(R:Join(Parsable, ArithmeticType)): with {
	evalArith: (MachineInteger, List TREE) -> Partial R;
#if ALDOC
\aspage{evalArith}
\Usage{\name(op,[$e_1,\dots,e_n$])}
\Signature
{(\astype{MachineInteger}, \astype{List} \astype{ExpressionTree})}
{\astype{Partial} R}
\Params{
{\em op} & \astype{MachineInteger} & Code for an operator\\
$e_i$ & \astype{ExpressionTree} & Expression trees\
}
\Retval{Returns the result of evaluating $op(e_1,\dots,e_n)$ where
$op$ is a code from {\tt include/uid.as}. Provides support for
the evaluation of the operators $+$, $-$, $\ast$ and $\hat{}$.}
#endif
	evalInt: TREE -> Partial Integer;
#if ALDOC
\aspage{evalInt}
\Usage{\name~e}
\Signature{\astype{ExpressionTree}}{\astype{Partial} \astype{Integer}}
\Params{ {\em e} & \astype{ExpressionTree} & An expression tree\\ }
\Retval{Returns the value of $e$ as an integer if it is an
integer--valued leaf, \failed otherwise.}
#endif
} == add {
	local maxint:Integer == (max$MachineInteger)::Integer;

	evalInt(t:TREE):Partial Integer == {
		import from Integer, LEAF;
		leaf? t => {
			l := leaf t;
			machineInteger? l => [machineInteger(l)::Integer];
			integer? l => [integer l];
			failed;
		}
		failed;
	}

	evalArith(op:MachineInteger, l:List TREE):Partial R == {
		import from Boolean, Partial Integer;
		TRACE("parsable::eval:op = ", op);
		TRACE("parsable::eval:l = ", l);
		op = UID__PLUS => {
			ans:R := 0;
			for arg in l repeat {
				u := eval arg;
				failed? u => return failed;
				ans := ans + retract u;
			}
			[ans];
		}
		op = UID__TIMES => {
			ans:R := 1;
			for arg in l repeat {
				u := eval arg;
				failed? u => return failed;
				ans := ans * retract u;
			}
			[ans];
		}
		op = UID__MINUS => {
			empty? l or failed?(u := eval first l) => failed;
			a := retract u;
			empty? rest l => [-a];
			~empty?(rest rest l) or
				failed?(u := eval first rest l) => failed;
			[a - retract u];
		}
		op = UID__EXPT => {
			empty? l or failed?(u := eval first l) or empty?(rest l)
				or ~empty?(rest rest l)
				or failed?(v := evalInt first rest l)
				or (e := retract v) < 0 or e > maxint => failed;
			[retract(u)^machine(e)];
		}
		failed;
	}
}

