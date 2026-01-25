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
---------------------------- sal_fstruc.as ----------------------------------
--
-- This file defines finite linear structures
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro Z == MachineInteger;

#if ALDOC
\thistype{FiniteLinearStructureType}
\History{Manuel Bronstein}{16/10/98}{created}
\Usage{\this~T: Category}
\Params{{\em T} & Type & the type of the entries\\}
\Descr{\this~is the category of finite linear structures whose entries are
of type T.}
\begin{exports}
\category{\astype{LinearStructureType} T}\\
\asexp{$+$}: & (\%, \astype{MachineInteger}) $\to$ \% & translate the base\\
\asexp{[]}: & \builtin{Tuple} T $\to$ \% & construction of a structure\\
\asexp{empty}: & \%  & empty structure\\
\asexp{empty?}:
& \% $\to$ \astype{Boolean} & test whether a structure is empty\\
\asexp{new}: & (\astype{MachineInteger}, T) $\to$ \% & creation of a structure\\
\end{exports}
#endif

define FiniteLinearStructureType(T:Type):Category == LinearStructureType T with{
	+: (%, Z) -> %;
#if ALDOC
\aspage{$+$}
\Usage{a \name~n}
\Signature{(\%, \astype{MachineInteger})}{\%}
\Params{
{\em a} & \% & a finite linear structure\\
{\em n} & \astype{MachineInteger} & an index\\
}
\Retval{$a\name n$ returns the substructure of $a$ starting at the
${(n+1)}^{{\rm st}}$ element of $a$, \ie $a + 0$ returns $a$, $a + 1$
returns the structure starting at the second element of $a$, etc\dots.
No copy of $a$ is made.}
\begin{asex}
If $a$ is the list of \astype{MachineInteger} $[1,2,3,4,5]$,
then $a + 2$ is the list $[3,4,5]$.
If $s$ is the \astype{String} ``Hello world!'', then $s + 6$ is the string
``world!''.
\end{asex}
#endif
	bracket: Tuple T -> %;
#if ALDOC
\aspage{[]}
\Usage{[$t_1,\dots,t_n$]}
\Signature{\builtin{Tuple} T}{\%}
\Params{ $t_1,\dots,t_n$ & T & elements of T\\ }
\Retval{Returns the structure $[t_1,\dots,t_n]$.}
#endif
	empty: %;
	empty?: % -> Boolean;
#if ALDOC
\aspage{empty}
\astarget{\name?}
\Usage{\name\\\name?~a}
\Signatures{
\name: \%\\
\name?: \% $\to$ \astype{Boolean}\\
}
\Params{ {\em a} & \% & a finite linear structure\\ }
\Retval{\name~returns an empty structure, while \name?(a) returns \true if
$a$ is the empty structure, \false otherwise.}
#endif
	new: (Z, T) -> %;
#if ALDOC
\aspage{new}
\Usage{\name(n, x)}
\Signature{(\astype{MachineInteger}, T)}{\%}
\Params{
{\em n} & \astype{MachineInteger} & a nonnegative size\\
{\em x} & T & an entry\\
}
\Retval{Returns a structure of $n$ entries, all of them set to $x$.}
#endif
}
