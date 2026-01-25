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
--------------------------   sit_OPmatrx.as   ------------------------
-- Copyright (c) Marco Codutti 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"
#include "uid"

#if ALDOC
\thistype{ExpressionTreeMatrix}
\History{Marco Codutti}{10 May 95}{created}
\Usage{import from \this}
\Descr{\this~is the matrix operator for expression trees.}
\begin{exports}
\category{\astype{ExpressionTreeOperator}}\\
\end{exports}
\begin{remarks}
The following function is not yet implemented and produces dummy results :
{\bf fortran}.
\end{remarks}
#endif
	
macro {
	Z	      == MachineInteger;
	TEXT	      == TextWriter;
	TREE 	 == ExpressionTree;
	FALSE      == (t:TREE):Boolean +-> false;
	RET        == new(1,newline);
}

ExpressionTreeMatrix : ExpressionTreeOperator == add
{
	import from String, TREE, ExpressionTreeOperatorTools;

	name:Symbol			== -"matrix";
	arity:Z				== -1;
	uniqueId:Z			== UID__MATRIX;
	texParen?(p:Z):Boolean   == false;

	aldor(p:TEXT,l:List TREE):TEXT	== 
		trav (p,l,aldor, "matrix [[", ",", "],[", "]]" );

	axiom(p:TEXT, l:List TREE):TEXT	==  
		trav (p,l,axiom, "matrix [[", ",", "],[", "]]" );

	lisp(p:TEXT, l:List TREE):TEXT	==  
		trav (p,l,lisp, "((", " ", ") (", "))" );

	local dimensions(l:List TREE):(Z, Z) == {
		import from TREE, ExpressionTreeLeaf;
		(machineInteger leaf first l, machineInteger leaf first rest l);
	}

	maple(p:TEXT, l:List TREE):TEXT	==   {
		import from Z;
		(n, m) := dimensions l;
		p << "linalg[matrix](" << n << "," << m;
		n = 0 or m = 0 => p << ",[])";
		trav (p,l,maple, ",[", ",", ",", "])" );
	}

	fortran(p:TEXT,l:List TREE):TEXT== p << "--- fortran matrix ---";

	C(p:TEXT,l:List TREE):TEXT	== {
		import from Z;
		(n, m) := dimensions l;
		p << "[" << n << "][" << m << "]{";
		infix( p, l, FALSE, C, "," );
		p << "}";
	}

	tex(p:TEXT, l:List TREE):TEXT == 
	{
		import from Character;
		b := "\pmatrix{" + RET;
		trav (p,l,tex, b, " & ", " \cr " + RET, "\cr } ");
	}

	-- return ([a_{n+1},...], [a_1,\dots,a_n]) where l = [a_1,...]
	local first(l:List TREE, n:Z):(List TREE, List TREE) == {
		import from Boolean;
		ll:List TREE := empty;
		for i in 1..n repeat {
			assert(~empty? l);
			ll := cons(first l, ll);
			l := rest l;
		}
		(l, reverse! ll);
	}

	local trav ( p:TEXT, l:List TREE, f:(TEXT,TREE)->TEXT, 
	       begin:String, sep1:String, sep2:String, end:String ) : TEXT ==
	{
		import from Z, Boolean;
		(n, m) := dimensions l;
		l := rest rest l;
		p << begin;
		for i in 1..prev n repeat {
			(l, lm) := first(l, m);
			infix( p, lm, FALSE, f, sep1 );
			p << sep2;
		}
		if ~empty?(l) then infix( p, l, FALSE, f, sep1 );
		p << end;
	}
}

