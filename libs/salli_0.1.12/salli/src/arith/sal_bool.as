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
------------------------------ sal_bool.as ----------------------------------
--
-- This file extends Boolean to its final salli category
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

#if ALDOC
\thistype{Boolean}
\History{Manuel Bronstein}{28/9/98}{created}
\Usage{import from \this}
\Descr{\this~implements the boolean values \true and \false.}
\begin{exports}
\category{\astype{BooleanArithmeticType}}\\
\category{\astype{HashType}}\\
\asexp{false}: & \% & \false\\
\asexp{true}: & \% & \true\\
\end{exports}

\aspage{true,false}
\astarget{true}
\astarget{false}
\Usage{true\\false}
\Signature{}{\%}
\Retval{true and false return the boolean values \true and \false
respectively.}
#endif

extend Boolean:Join(BooleanArithmeticType, HashType) == add {
	import from Machine;
	Rep == Bool;

	(a:%) /\ (b:%):%		== per(rep a /\ rep b);
	(a:%) \/ (b:%):%		== per(rep a \/ rep b);
	hash(a:%):MachineInteger	== { a => 1; 0 }

	-- TEMPORARY (BUG1182) DEFAULTS DON'T INLINE WELL
	xor(a:%, b:%):% == (a /\ ~b) \/ (~a /\ b);
}

#if ALDOC
\thistype{BooleanArithmeticType}
\History{Manuel Bronstein}{28/9/98}{created}
\Usage{\this: Category}
\Descr{\this~is the category of types allowing boolean arithmetic.}
\begin{exports}
\category{\astype{PrimitiveType}}\\
\asexp{\~~}: & \% $\to$ \% & negation\\
\asexp{$/\backslash$}: & (\%, \%) $\to$ \% & and\\
\asexp{$\backslash/$}: & (\%, \%) $\to$ \% & or\\
\asexp{xor}: & (\%, \%) $\to$ \% & exclusive or\\
\end{exports}
#endif

define BooleanArithmeticType:Category == PrimitiveType with {
	~: % -> %;
	/\: (%, %) -> %;
	\/: (%, %) -> %;
	xor: (%, %) -> %;
#if ALDOC
\aspage{$\backslash/,/\backslash$,xor,\~}
\astarget{$\backslash/$}
\astarget{$/\backslash$}
\astarget{xor}
\astarget{\~}
\Usage{\~~a\\a $/\backslash$ b\\a $\backslash/$ b\\xor(a, b)\\}
\Signatures{
\~~: & \% $\to$ \%\\
$/\backslash,\backslash/$,xor: & (\%,\%) $\to$ \%\\
}
\Params{ {\em a, b} & \% & elements of the type\\}
\Retval{$\tilde{}~a$ returns $not(a)$, while $a \backslash/ b$ returns
$(a~or~b)$, $a /\backslash b$ returns $(a~and~b)$,
and $\mbox{xor}(a, b)$ returns
$$
(a /\backslash \tilde{}~b) \backslash/ (~\tilde{}~a /\backslash b)\,.
$$
The semantics of $not$, $or$ and $and$ can be logical or bitwise,
depending on the actual type.}
\Remarks{For the type \astype{Boolean}, the difference between
$a \backslash/ b$ and {\tt a or b} is that $a \backslash/ b$ guarantees
that both expressions $a$ and $b$ are evaluated while {\tt a or b} may
evaluate only $a$ and return \true if $a$ evaluates to \true. There is a
similar difference between $a /\backslash b$ and {\tt a and b}.}
\begin{asex}
If a and b are the \astype{MachineInteger} 5 and 7, then
~$\tilde{}~a = -6$, $a /\backslash b = 5$, $a \backslash/ b = 7$ and
$\mbox{xor}(a,b) = 2$.
\end{asex}
#endif
	default xor(a:%, b:%):% == (a /\ ~b) \/ (~a /\ b);
}

