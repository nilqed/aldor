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
-------------------------- sit_OPfact.as --------------------------
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"
#include "uid"

#if ALDOC
\thistype{ExpressionTreeFactorial}
\History{Manuel Bronstein}{18/6/2000}{created}
\Usage{import from \this}
\Descr{\this~is the generalized factorial operator for expression trees.}
\begin{exports}
\category{\astype{ExpressionTreeOperator}}\\
\end{exports}
#endif

macro {
	Z	== MachineInteger;
	TEXT	== TextWriter;
	TREE 	== ExpressionTree;
}

ExpressionTreeFactorial:ExpressionTreeOperator == add {
	import from String, TREE, ExpressionTreeOperatorTools;

	name:Symbol			== -"factorial";
	arity:Z				== 3;
	uniqueId:Z			== UID__FACTORIAL;
	texParen?(p:Z):Boolean		== false;
	axiom(p:TEXT, l:List TREE):TEXT	== prefix(p, l, axiom, "factorial");
	aldor(p:TEXT,l:List TREE):TEXT	== prefix(p, l, aldor, "factorial");
	maple(p:TEXT, l:List TREE):TEXT	== prefix(p, l, maple, "factorial");
	fortran(p:TEXT,l:List TREE):TEXT== prefix(p, l, fortran, "factorial");
	C(p:TEXT, l:List TREE):TEXT	== prefix(p, l, C, "factorial");
	lisp(p:TEXT, l:List TREE):TEXT	== lisp(p, "factorial", l);

	tex(p:TEXT, l:List TREE):TEXT == {
		import from Integer, ExpressionTreeLeaf;
		a := first l; s := first rest l; n := first rest rest l;
		leaf? s and integer?(lf := leaf s)
			and (one?(st := integer lf) or st = -1) => {
			str := { st > 0 => "ov"; "und" };
			p << "{" << a << "}^{{\" <<str<< "erline " << n << "}}";
				
		}
		prefix(p, l, tex, "\factorial", "\left(", "\right)");
	}
}
