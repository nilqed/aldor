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
------------------------------   sit_OPcase.as   ------------------------------
-- Copyright (c) Marco Codutti 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"
#include "uid"

macro {
	TEXT == TextWriter;
	TREE == ExpressionTree;
	SI   == MachineInteger;

	NOTYET(a,b) == p << a << " output for " << b << " not yet implemented.";
}

#if ALDOC
\thistype{ExpressionTreeCase}
\History{Marco Codutti}{12 June 95}{created}
\Usage{import from \this}
\Descr{\this~is the {\em multi conditional} operator for expression trees.}
\begin{exports}
\category{\astype{ExpressionTreeOperator}}\\
\end{exports}
\begin{remarks}
The following functions are not yet implemented and produce dummy results :
{\bf axiom}, {\bf C}, {\bf fortran}, {\bf maple}.
\end{remarks}
#endif

ExpressionTreeCase: ExpressionTreeOperator == add
{
	import from String, TREE, ExpressionTreeLeaf;

	name:Symbol             == -"case";
	arity:SI                == -1;
	uniqueId:SI             == UID__CASE;
	texParen?(p:SI):Boolean == true;

	aldor  (p:TEXT, l:List TREE): TEXT == {
		import from Boolean;
		empty? l => p << "case()";
		p := p << "case(";
		t := l;
		o := first t; t := rest  t;
		c := first t; t := rest  t;
		p := aldor (p, ExpressionTreeIf [ c, o ] );
		while ~empty? t repeat {
			o := first t; t := rest  t;
			c := first t; t := rest  t;
			p := p << ",";
			p := aldor (p, ExpressionTreeIf [ c, o ] );
		}
		p << ")";
	}

	axiom   (p:TEXT, l:List TREE): TEXT == NOTYET("axiom",name);
	C       (p:TEXT, l:List TREE): TEXT == NOTYET("C",name);
	fortran (p:TEXT, l:List TREE): TEXT == NOTYET("fortran",name);
	lisp   (p:TEXT, l:List TREE): TEXT == NOTYET("lisp",name);

	maple   (p:TEXT, l:List TREE): TEXT == {
		import from Boolean;
		t := l;
		empty? t => p << "()";
		leaf? (c:=first rest t) and string? (s := leaf(c)) 
			and string s = "always" => p << first t;
		p := p << "piecewise(";
		while ~empty? t repeat {
			o := first t; t := rest  t;
			c := first t; t := rest  t;
			p := maple(p, c); p := p << ","; p := maple(p, o);
			if ~empty? t then p := p << ",";
		}
		p << ")";
	}

	tex (p:TEXT, l:List TREE): TEXT == {
		import from Boolean;
		t := l;
		empty? t => p << "\left\{ \mbox{\em no case} \right.";
		leaf? (c:=first rest t) and string? (s := leaf(c)) 
			and string s = "always" => p << first t;
		p := p << "\left\{ \begin{array}{ll}";
		while ~empty? t repeat {
			o := first t; t := rest  t;
			c := first t; t := rest  t;
			p := tex (p,o); p := p << " & \mbox{if } ";
			p := tex (p,c); p := p << " \\";
		}
		p << "\end{array} \right.";
	}
}

