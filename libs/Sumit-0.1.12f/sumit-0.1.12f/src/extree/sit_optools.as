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
-------------------------- sit_optools.as --------------------------
--
-- Tools for generic operator methods
--
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{ExpressionTreeOperatorTools}
\History{Manuel Bronstein}{21/11/94}{created}
\Usage{import from \this}
\Descr{\this~provides utilities that make it simpler to write new operator
types.}
\begin{exports}
\asexp{infix}: & (TEXT, \astype{List} TREE, TREE $\to$ \astype{Boolean}, & \\
& ~~~(TEXT, TREE) $\to$ TEXT, & \\
& ~~~\astype{String}, \astype{String}, \astype{String}) $\to$ TEXT &
Write as infix\\
\asexp{prefix}: & (TEXT, \astype{List} TREE, & \\
& ~~~(TEXT, TREE) $\to$ TEXT, & \\
& ~~~\astype{String}, \astype{String}, \astype{String}) $\to$ TEXT &
Write as prefix\\
\end{exports}
\begin{aswhere}
TEXT &==& \astype{TextWriter}\\
TREE &==& \astype{ExpressionTree}\\
\end{aswhere}
#endif

macro {
	TEXT	== TextWriter;
	TREE 	== ExpressionTree;
}

ExpressionTreeOperatorTools: with {
	infix: (TEXT, List TREE, TREE -> Boolean, (TEXT, TREE) -> TEXT,
		String, lp:String == "(", rp:String == ")") -> TEXT;
#if ALDOC
\aspage{infix}
\Usage{\name(p, [$t_1,\dots,t_n$], paren?, farg, op, left, right)}
\Signature{(TEXT, \astype{List} TREE, TREE $\to$ \astype{Boolean},
(TEXT, TREE) $\to$ TEXT,\\
& ~~~\astype{String}, \astype{String}, \astype{String})}
{TEXT}
\Params{
{\em p} & TEXT & The port to write to\\
{\em [$t_1,\dots,t_n$]} & \astype{List} TREE & The arguments of the operator\\
{\em paren?} & TREE $\to$ \astype{Boolean} & The parenthetization function\\
{\em farg} & (TEXT, TREE) $\to$ TEXT & The function for the arguments\\
{\em op} & \astype{String} & The infix symbol\\
{\em left} & \astype{String} & The left parenthesis (optional)\\
{\em right} & \astype{String} & The right parenthesis (optional)\\
}
\begin{aswhere}
TEXT &==& \astype{TextWriter}\\
TREE &==& \astype{ExpressionTree}\\
\end{aswhere}
\Descr{Writes $farg(t_1)~op~\dots~op~farg(t_n)$ to $p$, calling $farg$
on each argument, and calling $paren?$ to decide whether to parenthetize
each argument. Uses $left$ and $right$, which default to ``('' and ``)''
when parenthetizing.}
\seealso{\asexp{prefix}}
#endif
	lisp: (TEXT, String, List TREE) -> TEXT;
#if ALDOC
\aspage{lisp}
\Usage{\name(p, s, [$t_1,\dots,t_n$])}
\Signature{(TEXT, \astype{String}, \astype{List} TREE)}{TEXT}
\Params{
{\em p} & TEXT & The port to write to\\
{\em s} & \astype{String} & A Lisp operator name\\
{\em [$t_1,\dots,t_n$]} & \astype{List} TREE & The arguments of the operator\\
}
\Descr{Writes $(s t_1 \dots t_n)$ to $p$, where each $t_i$ is written
in Lisp format.}
#endif
	prefix: (TEXT, TREE, TREE -> Boolean, (TEXT, TREE) -> TEXT,
		String, lp:String == "(", rp:String == ")") -> TEXT;
	prefix: (TEXT, List TREE, (TEXT, TREE) -> TEXT,
		String, lp:String == "(", rp:String == ")") -> TEXT;
#if ALDOC
\aspage{prefix}
\Usage{
\name(p, t, paren?, farg, op, left, right)\\
\name(p, [$t_1,\dots,t_n$], farg, op, left, right)
}
\Signatures{
\name: & (TEXT, TREE, TREE $\to$ \astype{Boolean}, (TEXT, TREE) $\to$ TEXT,\\
 & \phantom{name:}~~~\astype{String}, \astype{String}, \astype{String})
$\to$ TEXT\\
\name: & (TEXT, \astype{List} TREE, (TEXT, TREE) $\to$ TEXT,\\
 & \phantom{name:}~~~\astype{String}, \astype{String}, \astype{String})
$\to$ TEXT\\
}
\Params{
{\em p} & TEXT & The port to write to\\
{\em [$t_1,\dots,t_n$]} & \astype{List} TREE & The arguments of the operator\\
{\em paren?} & TREE $\to$ \astype{Boolean} & The parenthetization function\\
{\em farg} & (TEXT, TREE) $\to$ TEXT & The function for the arguments\\
{\em op} & \astype{String} & The prefix symbol\\
{\em left} & \astype{String} & The left parenthesis (optional)\\
{\em right} & \astype{String} & The right parenthesis (optional)\\
}
\begin{aswhere}
TEXT &==& \astype{TextWriter}\\
TREE &==& \astype{ExpressionTree}\\
\end{aswhere}
\Descr{Writes $op(farg(t_1),\dots,farg(t_n))$ to $p$, calling $farg$
on each argument. Uses $left$ and $right$, which default to ``('' and ``)''
for parenthetizing. The unary version calls $paren?$ to decide whether
to parenthetize the argument.}
\seealso{\asexp{infix}}
#endif
} == add {
	import from MachineInteger;

	local alwaysTrue(t:TREE):Boolean == true;

        prefix(p:TEXT, t:TREE, par?:TREE -> Boolean, f:(TEXT,TREE) -> TEXT,
		op:String, lp:String, rp:String):TEXT == {
			p := p << op;
			paren? := par? t;
			if paren? then p := p << lp;
			p := f(p, t);
			paren? => p << rp;
			p;
	}

        prefix(p:TEXT, l:List TREE, f:(TEXT,TREE) -> TEXT,
		op:String, lp:String, rp:String):TEXT == {
			p := p << op << lp;
			for t in l for i in #l.. by -1 repeat {
				p := f(p, t);
				if i > 1 then p := p << ",";
			}
			p << rp;
	}

        infix(p:TEXT, l:List TREE, par?:TREE -> Boolean, f:(TEXT,TREE) -> TEXT,
		op:String, lp:String, rp:String):TEXT == {
			empty? l => p;
			empty? rest l => f(p, first l);
			paren? := par? first l;
			if paren? then p := p << lp;
			p := f(p, first l);
			for t in rest l repeat {
				if paren? then p := p << rp;
				p := p << op;
				paren? := par? t;
				if paren? then p := p << lp;
				p := f(p, t);
			}
			paren? => p << rp;
			p;
	}

	lisp(p:TEXT, s:String, l:List TREE):TEXT == {
		import from TREE;
		p := p << "(" << s;
		for arg in l repeat p := lisp(p << " ", arg);
		p << ")";
	}
}
