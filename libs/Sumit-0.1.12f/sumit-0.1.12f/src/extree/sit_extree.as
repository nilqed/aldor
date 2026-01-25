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
------------------------------- sit_extree.as ----------------------------------
--
-- Inert Expression Trees
--
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "sumit"
#include "op"
#include "leaf"
#include "uid"

#if ALDOC
\thistype{ExpressionTree}
\History{Manuel Bronstein}{24/11/94}{created}
\Usage{import from \this}
\Descr{\this~is a type whose elements are expression trees.}
\begin{exports}
\category{\astype{OutputType}}\\
\category{\astype{PrimitiveType}}\\
\asexp{aldor}: & (TEXT, \%) $\to$ TEXT & Conversion to \asharp code\\
\asexp{apply}:
& (OP, \astype{List} \%) $\to$ \% & Apply an operator to arguments\\
\asexp{apply}:
& (OP, \builtin{Tuple} \%) $\to$ \% & Apply an operator to arguments\\
\asexp{arguments}:
& \% $\to$ \astype{List} \% & Take the arguments of the root\\
\asexp{axiom}: & (TEXT, \%) $\to$ TEXT & Conversion to Axiom code\\
\asexp{C}: & (TEXT, \%) $\to$ TEXT & Conversion to C code\\
\asexp{extree}: & \astype{ExpressionTreeLeaf} $\to$ \% & Conversion to a tree\\
\asexp{fortran}: & TEXT, \%) $\to$ TEXT & Conversion to FORTRAN code\\
\asexp{is?}: & (\%, OP) $\to$ \astype{Boolean} & Test for a specific operator\\
\asexp{leaf}: & \% $\to$ \astype{ExpressionTreeLeaf} & Conversion to a leaf\\
\asexp{leaf?}: & \% $\to$ \astype{Boolean} & Test whether tree is a leaf\\
\asexp{lisp}: & TEXT, \%) $\to$ TEXT & Conversion to Lisp code\\
\asexp{maple}: & (TEXT, \%) $\to$ TEXT & Conversion to Maple code\\
\asexp{operator}: & \% $\to$ OP & Take the root operator\\
\asexp{tex}: & (TEXT, \%) $\to$ TEXT & Conversion to \LaTeX\\
\asexp{texParen?}: & \% $\to$ \astype{Boolean} & Check whether to parenthetize\\
\end{exports}
\begin{aswhere}
TEXT &==& \astype{TextWriter}\\
OP &==& \astype{ExpressionTreeOperator}\\
\end{aswhere}
#endif

ExpressionTree: Join(OutputType, PrimitiveType) with {
	aldor:		(TEXT, %) -> TEXT;
	axiom:		(TEXT, %) -> TEXT;
	C:		(TEXT, %) -> TEXT;
	fortran:	(TEXT, %) -> TEXT;
	lisp:		(TEXT, %) -> TEXT;
	maple:		(TEXT, %) -> TEXT;
	tex:		(TEXT, %) -> TEXT;
#if ALDOC
\aspage{aldor,axiom,C,fortran,lisp,maple,tex}
\astarget{aldor}
\astarget{axiom}
\astarget{C}
\astarget{fortran}
\astarget{lisp}
\astarget{maple}
\astarget{tex}
\Usage{{\em format}(p, t)}
\Signature{(\astype{TextWriter}, \%)}{\astype{TextWriter}}
\Params{
{\em p} & \astype{TextWriter} & The port to write to\\
{\em t} & \% & An expression tree\\
}
\Descr{Writes to $p$ the expression corresponding to the tree $t$
in the requested format.}
#endif
	--apply:		(OP, Tuple %) -> %;   compiler bug
	apply:		(OP, List %) -> %;
#if ALDOC
\aspage{apply}
\Usage{
\name(op, $t_1,\dots,t_n$)\\ \name(op, [$t_1,\dots,t_n$])\\
op($t_1,\dots,t_n$)\\ op~[$t_1,\dots,t_n$]
}
\Signatures{
\name: & \astype{List} \% $\to$ \%\\
\name: & \builtin{Tuple} \% $\to$ \%\\
}
\Params{
{\em op} & \astype{ExpressionTreeOperator} & An operator\\
{\em $t_i$} & \% & Expression trees\\
}
\Retval{Returns the tree whose root is $op$, with arguments $t_1,\dots,t_n$.}
#endif
	arguments:	% -> List %;
#if ALDOC
\aspage{arguments}
\Usage{\name~t}
\Signature{\%}{\astype{List} \%}
\Params{ {\em t} & \% & An expression tree\\ }
\Retval{Returns the list of arguments of the root operator of $t$, which must
not be a leaf.}
\seealso{\asexp{operator}}
#endif
	extree:		ExpressionTreeLeaf -> %;
#if ALDOC
\aspage{extree}
\Usage{\name~a}
\Signature{\astype{ExpressionTreeLeaf}}{\%}
\Params{ {\em a} & \astype{ExpressionTreeLeaf} & A leaf\\ }
\Retval{\name~a returns $a$ as an expression tree.}
#endif
	is?:		(%, OP) -> Boolean;
#if ALDOC
\aspage{is?}
\Usage{\name(t, op)}
\Signature{(\%, \astype{ExpressionTreeOperator})}{\astype{Boolean}}
\Params{
{\em t} & \% & An expression tree\\
{\em op} & \astype{ExpressionTreeOperator} & An operator\\
}
\Retval{\name(t, op) returns \true~if t is of the form op(args),
\false~otherwise.}
#endif
	leaf:		% -> ExpressionTreeLeaf;
	leaf?:		% -> Boolean;
#if ALDOC
\aspage{leaf}
\astarget{\name?}
\Usage{ \name~t\\ \name?~t }
\Signatures{
\name: & \% $\to$ \astype{ExpressionTreeLeaf}\\
\name?: & \% $\to$ \astype{Boolean}\\
}
\Params{ {\em t} & \% & An expression tree\\ }
\Retval{
\name~a returns $a$ as a leaf is $a$ is a leaf.
\name?~a returns \true~if a is a leaf, \false~otherwise.
}
#endif
	negate:		% -> %;
#if ALDOC
\aspage{negate}
\Usage{\name~t}
\Signature{\%}{\%}
\Params{ {\em t} & \% & An expression tree\\ }
\Retval{Returns the leaf $-t$ if $t$ is a numerical leaf with $t < 0$,
and returns $s$ if $t$ is of the form $(- s)$ for some tree $s$.
$t$ must be of one of the above 2 forms.}
\seealso{\asexp{negative?}}
#endif
	negative?:	% -> Boolean;
#if ALDOC
\aspage{negative?}
\Usage{\name~t}
\Signature{\%}{\astype{Boolean}}
\Params{ {\em t} & \% & An expression tree\\ }
\Retval{Returns \true~if either $t$ is a numerical leaf and $t < 0$,
or if $t$ is of the form $(- s)$ for some tree $s$, \false~otherwise.}
\seealso{\asexp{negate}}
#endif
	operator:	% -> OP;
#if ALDOC
\aspage{operator}
\Usage{\name~t}
\Signature{\%}{\astype{ExpressionTreeOperator}}
\Params{ {\em t} & \% & An expression tree\\ }
\Retval{Returns the root operator of $t$, which must not be a leaf.}
\seealso{\asexp{arguments}}
#endif
	texParen?:	(Z, %) -> Boolean;
#if ALDOC
\aspage{texParen?}
\Usage{\name(prec, t)}
\Signature{(\astype{MachineInteger}, \%)}{\astype{Boolean}}
\Params{
{\em prec} & \astype{MachineInteger} & An operator precendence.\\
{\em t} & \% & An expression tree\\
}
\Retval{Returns \true~if $t$ should be parenthetized when appearing as
argument of an operator of precedence {\em prec}, \false~otherwise.}
#endif
} == add {
	macro {
		Tree == Record(oper:OP, argum: List %);
		Leaf == ExpressionTreeLeaf;
		Rep == Union(uleaf: Leaf, utree: Tree);
	}

	import from Rep;

	-- sample:%			== per [sample$Leaf];
	extree(l:Leaf):%		== per [l];
	local tree(r:Tree):%		== per [r];
	--apply(op:OP, t:Tuple %):%	== tree [op, list t];
	apply(op:OP, l:List %):%	== tree [op, l];
	leaf?(t:%):Boolean		== rep(t) case uleaf;
	leaf(t:%):Leaf			== { assert(leaf? t); rep(t).uleaf; }
	operator(t:%):OP		== operator tree t;
	arguments(t:%):List %		== arguments tree t;
	local operator(t:Tree):OP	== t.oper;
	local arguments(t:Tree):List %	== t.argum;
	texParen?(p:Z, t:Tree):Boolean	== texParen?(p)$operator(t);
	tex(p:TEXT, t:%):TEXT		== switchon(p, t, tex, tex);
	axiom(p:TEXT, t:%):TEXT		== switchon(p, t, axiom, axiom);
	maple(p:TEXT, t:%):TEXT		== switchon(p, t, maple, maple);
	C(p:TEXT, t:%):TEXT		== switchon(p, t, C, C);
	fortran(p:TEXT, t:%):TEXT	== switchon(p, t, fortran, fortran);
	lisp(p:TEXT, t:%):TEXT		== switchon(p, t, lisp, lisp);
	aldor(p:TEXT, t:%):TEXT		== switchon(p, t, aldor, aldor);
	is?(t:%, op:OP):Boolean		== (~leaf? t) and is?(tree t, op);
	local tex(p:TEXT, t:Tree):TEXT	== tex(p, arguments t)$operator(t);
	local axiom(p:TEXT,t:Tree):TEXT	== axiom(p, arguments t)$operator(t);
	local maple(p:TEXT,t:Tree):TEXT	== maple(p, arguments t)$operator(t);
	local aldor(p:TEXT,t:Tree):TEXT== aldor(p, arguments t)$operator(t);
	local fortran(p:TEXT,t:Tree):TEXT== fortran(p, arguments t)$operator(t);
	local lisp(p:TEXT,t:Tree):TEXT	== lisp(p, arguments t)$operator(t);
	local C(p:TEXT, t:Tree):TEXT	== C(p, arguments t)$operator(t);
	local negate(t:Tree):%	== { assert negative? t; first arguments t; }

	local tree(t:%):Tree == {
		import from Boolean;
		assert(~leaf? t);
		rep(t).utree;
	}

	local is?(t:Tree, op:OP):Boolean == {
		import from Z;
		uniqueId$operator(t) = uniqueId$op;
	}

	local negative?(t:Tree):Boolean == {
		import from Z;
		uniqueId$operator(t) = UID__MINUS;
	}

	local opeq(x:%, y:%):Boolean == {
		import from Z;
		uniqueId$operator(x) = uniqueId$operator(y);
	}

	negative?(t:%):Boolean == {
		leaf? t => negative? leaf t;
		negative? tree t;
	}

	negate(t:%):% == {
		leaf? t => extree negate leaf t;
		negate tree t;
	}

	(p:TEXT) << (t:%):TEXT == {
		leaf? t => p << leaf t;
		stream(p, tree t); -- cannot use operator(t) in this function
	}

	local stream(p:TEXT, t:Tree):TEXT == {
		import from String, Symbol;
		p := p << "(" << name$operator(t);
		for a in arguments t repeat p := p << " " << a;
		p << ")";
	}

	(x:%) = (y:%):Boolean == {
		leaf? x => leaf? y and leaf x = leaf y;
		-- cannot use operator(t) in this function
		(~leaf? y) and arguments x = arguments y and opeq(x, y)
	}

	local switchon(p:TEXT, t:%, f:(TEXT, Leaf) -> TEXT,
		g:(TEXT, Tree) -> TEXT):TEXT == {
			leaf? t => f(p, leaf t);
			g(p, tree t);
	}

	texParen?(p:Z, t:%):Boolean == {
		leaf? t => texParen? leaf t;
		texParen?(p, tree t);
	}
}

#if SUMITTEST
---------------------- test extree.as --------------------------
#include "sumittest"

macro {
	Z		== MachineInteger;
	Plus		== ExpressionTreePlus;
	Minus		== ExpressionTreeMinus;
	Times		== ExpressionTreeTimes;
	Expt		== ExpressionTreeExpt;
	Quotient	== ExpressionTreeQuotient;
	Tree		== ExpressionTree;
}

height(t:Tree):Z == {
	import from List Tree;
	m:Z := 1;
	leaf? t => m;
	for a in arguments t repeat {
		h := height a;
		if h > m then m := h;
	}
	m + 1;
}

extree0(t:Tree):Boolean == {
	import from Z, String, Symbol, List Tree;
	2 = arity$operator(t) and name$operator(first arguments t) = -"+";
}

extree():Boolean == {
	import from Z, String, Symbol, SingleFloat;
	import from Tree, List Tree, ExpressionTreeLeaf;

	x := extree leaf(-"x");
	y := extree leaf(-"y");

	t2 := extree leaf 2;
	t3 := extree leaf 3;

	-- t is the fraction ((x-1.5)y^3 + 2x^2y^2 + (x+2)^3 y+x+1) / (y-2)

	t := Plus [Times [Plus [x, Minus [extree leaf 1.5]], Expt [y, t3]],_
		Times [t2, Expt [x, t2], Expt [y, t2]],_
		Times [Expt [Plus [x, t2], t3], y], x, extree leaf(1@Z)];

	t := Quotient [t, Plus [y, Minus [t2]]];

	6 = height t and extree0 t;
}

stdout << "Testing sit__extree..." << endnl;
sumitTest("extree", extree);
stdout << endnl;
#endif

