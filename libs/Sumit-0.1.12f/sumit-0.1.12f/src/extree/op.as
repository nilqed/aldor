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
------------------------------- op.as ----------------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1994
--
-- This type must be included inside "extree.as" to be compiled,
-- but is in a separate file for documentation purposes.

#if ALDOC
\thistype{ExpressionTreeOperator}
\History{Manuel Bronstein}{21/11/94}{created}
\Usage{\this: Category}
\Descr{\this~is the category of operators for expression trees.}
\begin{exports}
\asexp{aldor}:
& (TEXT, \astype{List} TREE) $\to$ TEXT & Conversion to \asharp code\\
\asexp{arity}: & \astype{MachineInteger} & Number of arguments\\
\asexp{axiom}:
& (TEXT, \astype{List} TREE) $\to$ TEXT & Conversion to Axiom code\\
\asexp{C}: & (TEXT, \astype{List} TREE) $\to$ TEXT & Conversion to C code\\
\asexp{fortran}:
& (TEXT, \astype{List} TREE) $\to$ TEXT & Conversion to FORTRAN code\\
\asexp{lisp}:
& (TEXT, \astype{List} TREE) $\to$ TEXT & Conversion to Lisp code\\
\asexp{maple}:
& (TEXT, \astype{List} TREE) $\to$ TEXT & Conversion to Maple code\\
\asexp{name}: &	\astype{Symbol} & Operator name\\
\asexp{tex}: & (TEXT, \astype{List} TREE) $\to$ TEXT & Conversion to \LaTeX\\
\asexp{texParen?}: & \astype{MachineInteger} $\to$ \astype{Boolean} &
Check whether to parenthetize\\
\asexp{uniqueId}: & \astype{MachineInteger} & A unique key per operator\\
\end{exports}
\begin{aswhere}
TEXT &==& \astype{TextWriter}\\
TREE &==& \astype{ExpressionTree}\\
\end{aswhere}
#endif

macro {
	Z	== MachineInteger;
	OP	== ExpressionTreeOperator;
	TEXT	== TextWriter;
	TREE	== ExpressionTree;
}

define ExpressionTreeOperator: Category == with {
	aldor:		(TEXT, List TREE) -> TEXT;
	axiom:		(TEXT, List TREE) -> TEXT;
	C:		(TEXT, List TREE) -> TEXT;
	fortran:	(TEXT, List TREE) -> TEXT;
	lisp:		(TEXT, List TREE) -> TEXT;
	maple:		(TEXT, List TREE) -> TEXT;
	tex:		(TEXT, List TREE) -> TEXT;
#if ALDOC
\aspage{aldor,axiom,C,fortran,lisp,maple,tex}
\astarget{aldor}
\astarget{axiom}
\astarget{C}
\astarget{fortran}
\astarget{lisp}
\astarget{maple}
\astarget{tex}
\Usage{{\em format}(p, [$t_1,\dots,t_n$])}
\Signature{(\astype{TextWriter}, \astype{List} \astype{ExpressionTree})}{\astype{TextWriter}}
\Params{
{\em p} & \astype{TextWriter} & The port to write to\\
{\em $t_i$} & \astype{ExpressionTree} & The arguments of the operator\\
}
\Descr{Writes to $p$ the expression corresponding to this operator applied to
the arguments $(t_1,\dots,t_n)$ in the requested format.}
#endif
	arity:		Z;
#if ALDOC
\aspage{arity}
\Usage{\name}
\Signature{}{\astype{MachineInteger}}
\Retval{Returns $-1$ if this operator can be applied to any number of arguments,
$n \ge 0$ if this operator can be applied to exactly $n$ arguments.}
#endif
	name:		Symbol;
#if ALDOC
\aspage{name}
\Usage{\name}
\Signature{}{\astype{Symbol}}
\Retval{Returns the name of this operator.}
#endif
	texParen?:	Z -> Boolean;
#if ALDOC
\aspage{texParen?}
\Usage{\name~prec}
\Signature{\astype{MachineInteger}}{\astype{Boolean}}
\Params{ {\em prec} & \astype{MachineInteger} & An operator precendence.\\ }
\Retval{Returns \true~if an expression tree with this operator as root should
be parenthetized when appearing as argument of an operator of precedence
{\em prec}, \false~otherwise.}
#endif
	uniqueId:	Z;
#if ALDOC
\aspage{uniqueId}
\Usage{\name}
\Signature{}{\astype{MachineInteger}}
\Retval{Returns a integer key which is associated to this operator only.
This is used for testing whether two operators are equal.}
#endif
	default {
		lisp(p:TEXT, l:List TREE):TEXT == {
			import from TREE, String, Symbol;
			p := p << "(" << name;
			for arg in l repeat p := lisp(p << " ", arg);
			p << ")";
		}
	}
}

