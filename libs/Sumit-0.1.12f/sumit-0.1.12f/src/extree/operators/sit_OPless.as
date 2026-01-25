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
------------------------------   sit_OPless.as   ------------------------------
-- Copyright (c) Manuel Bronstein 1995
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
\thistype{ExpressionTreeLessEqual}
\History{Manuel Bronstein}{15 December 97}{created}
\Usage{import from \this}
\Descr{\this~is the {\em less or equal} operator for expression trees.}
\begin{exports}
\category{\astype{ExpressionTreeOperator}}\\
\end{exports}
\begin{remarks}
The following functions are not yet implemented and produce dummy results :
{\bf C}, {\bf fortran}, {\bf lisp}.
\end{remarks}
#endif
   
ExpressionTreeLessEqual: ExpressionTreeOperator == add
{
	import from String, TREE;

	name:Symbol             == -"<=";
	arity:SI                == 2;
	uniqueId:SI             == UID__LESSEQUAL;
	texParen?(p:SI):Boolean == true;

	aldor  (p:TEXT, l:List TREE): TEXT == INFIX2(aldor,p,l,"<=");
	axiom   (p:TEXT, l:List TREE): TEXT == INFIX2(axiom,p,l,"<=");
	C       (p:TEXT, l:List TREE): TEXT == NOTYET("C","<=");
	fortran (p:TEXT, l:List TREE): TEXT == NOTYET("fortran","<=");
	maple   (p:TEXT, l:List TREE): TEXT == INFIX2(maple,p,l,"<=");
	tex     (p:TEXT, l:List TREE): TEXT == INFIX2(tex,p,l,"\le ");
	lisp	(p:TEXT, l:List TREE): TEXT == NOTYET("lisp", "<=");
}

#if ALDOC
\thistype{ExpressionTreeLessThan}
\History{Manuel Bronstein}{15 December 97}{created}
\Usage{import from \this}
\Descr{\this~is the {\em less than} operator for expression trees.}
\begin{exports}
\category{\astype{ExpressionTreeOperator}}\\
\end{exports}
\begin{remarks}
The following functions are not yet implemented and produce dummy results :
{\bf C}, {\bf fortran}, {\bf lisp}.
\end{remarks}
#endif

ExpressionTreeLessThan: ExpressionTreeOperator == add
{
	import from String, TREE;

	name:Symbol             == -"<";
	arity:SI                == 2;
	uniqueId:SI             == UID__LESSTHAN;
	texParen?(p:SI):Boolean == true;

	aldor  (p:TEXT, l:List TREE): TEXT == INFIX2(aldor,p,l,"<");
	axiom   (p:TEXT, l:List TREE): TEXT == INFIX2(axiom,p,l,"<");
	C       (p:TEXT, l:List TREE): TEXT == NOTYET("C","<");
	fortran (p:TEXT, l:List TREE): TEXT == NOTYET("fortran","<");
	maple   (p:TEXT, l:List TREE): TEXT == INFIX2(maple,p,l,"<");
	tex     (p:TEXT, l:List TREE): TEXT == INFIX2(tex,p,l,"<");
	lisp	(p:TEXT, l:List TREE): TEXT == NOTYET("lisp", "<");
}
