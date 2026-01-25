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
----------------------------- sit_pable.as ----------------------------------
--
-- Expression Tree Arithmetic Interpreters
--
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"
#include "uid"

macro {
	TREE	== ExpressionTree;
	LEAF	== ExpressionTreeLeaf;
}

#include "sit_ptools"

#if ALDOC
\thistype{Parsable}
\History{Manuel Bronstein}{30/08/99}{created}
\Usage{\this: Category}
\Descr{\this~is the category of types that convert
expression trees into themselves whenever possible.}
\begin{exports}
\category{\astype{InputType}}\\
\asexp{eval}: & \astype{ExpressionTree} $\to$ \astype{Partial} \% &
Interpret a tree\\
\asexp{eval}: & \astype{ExpressionTreeLeaf} $\to$ \astype{Partial} \% &
Interpret a leaf\\
\asexp{eval}:
& (\astype{MachineInteger}, \astype{List} \astype{ExpressionTree})
$\to$ \astype{Partial} \% & Interpret a node\\
\end{exports}
#endif

define Parsable: Category == InputType with {
	eval:	TREE -> Partial %;
	eval:	LEAF -> Partial %;
	eval:	(MachineInteger, List TREE) -> Partial %;
#if ALDOC
\aspage{eval}
\Usage{\name~e\\ \name~t\\ \name(op,[$e_1,\dots,e_n$])}
\Signatures{
\name: & \astype{ExpressionTree} $\to$ \astype{Partial} \%\\
\name: & \astype{ExpressionTreeLeaf} $\to$ \astype{Partial} \%\\
\name: & (\astype{MachineInteger}, \astype{List} \astype{ExpressionTree})
$\to$ \astype{Partial} \%\\
}
\Params{
{\em e},$e_i$ & \astype{ExpressionTree} & Expression trees\\
{\em t} & \astype{ExpressionTreeLeaf} & A leaf\\
{\em op} & \astype{MachineInteger} & Code for an operator\\
}
\Retval{\name(e) and \name(t) return the result of evaluating the
given tree or leaf in the type, while \name(op,[$e_1,\dots,e_n$])
returns the result of evaluating $op(e_1,\dots,e_n)$ in the type,
where $op$ is a code from {\tt include/uid.as}.}
#endif
	default {
		eval(t:TREE):Partial % == {
			TRACE("parsable::eval ", t);
			leaf? t => eval leaf t;
			evalOp t;
		}

		local evalOp(t:TREE):Partial % == {
			import from Boolean;
			TRACE("parsable::evalOp ", t);
			assert(~leaf? t);
			eval(uniqueId$operator(t), arguments t);
		}

		<< (port:TextReader):% == {
			import from InfixExpressionParser;
			import from Partial TREE, Partial %;
			retract eval retract parse! parser port;
		}
	}
}
