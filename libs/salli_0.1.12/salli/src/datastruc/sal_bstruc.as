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
---------------------------- sal_bstruc.as ----------------------------------
--
-- This file defines bounded finite linear structures
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro Z == MachineInteger;

#if ALDOC
\thistype{BoundedFiniteLinearStructureType}
\History{Manuel Bronstein}{16/10/98}{created}
\Usage{\this~T: Category}
\Params{{\em T} & Type & the type of the entries\\}
\Descr{\this~is the category of finite linear structures whose entries are
of type T and whose size is always known.}
\begin{exports}
\category{\astype{CopyableType}}\\
\category{\astype{FiniteLinearStructureType} T}\\
\asexp{\#}: & \% $\to$ \astype{MachineInteger} & number of entries\\
\asexp{generator}:
& \% $\to$ \astype{Generator} T & iteration over a structure\\
\asexp{map}: & (T $\to$ T) $\to$ \% $\to$ \% & lift a mapping\\
\asexp{map!}: & (T $\to$ T) $\to$ \% $\to$ \% & lift a mapping\\
\end{exports}
\begin{exports}[if $T$ has \astype{PrimitiveType} then]
\category{\astype{PrimitiveType}}\\
\asexp{find}: & (T, \%) $\to$ (\%, \astype{MachineInteger}) & linear search\\
\asexp{member?}: & (T, \%) $\to$ \astype{Boolean} & check for a value\\
\end{exports}
\begin{exports}[if $T$ has \astype{HashType} then]
\category{\astype{HashType}}\\
\end{exports}
\begin{exports}[if $T$ has \astype{InputType} then]
\category{\astype{InputType}}\\
\end{exports}
\begin{exports}[if $T$ has \astype{OutputType} then]
\category{\astype{OutputType}}\\
\end{exports}
\begin{exports}[if $T$ has \astype{SerializableType} then]
\category{\astype{SerializableType}}\\
\end{exports}
#endif

define BoundedFiniteLinearStructureType(T:Type):Category ==
	Join(CopyableType, FiniteLinearStructureType T) with{
	if T has HashType then HashType;
	if T has InputType then InputType;
	if T has OutputType then OutputType;
	if T has SerializableType then SerializableType;
	#: % -> Z;
#if ALDOC
\aspage{\#}
\Usage{\name~a}
\Signature{\%}{\astype{MachineInteger}}
\Params{ {\em a} & \% & a finite linear structure\\ }
\Retval{Returns the number of entries in the structure $a$.}
#endif
	if T has PrimitiveType then {
		find: (T, %) -> (%, Z);
#if ALDOC
\aspage{find}
\Usage{\name(t, a)}
\Signature{(T, \%)}{(\%, \astype{MachineInteger})}
\Params{
{\em t} & T & the value to search for\\
{\em a} & \% & a finite linear structure\\
}
\Retval{Returns (b, i) such that:
\begin{itemize}
\item if b is not \asfunc{LinearStructureType}{empty},
then $a.i = t$ is the first occurence
of t in a, and b is the substructure of a starting at $a.i$,
\item if b is \asfunc{LinearStructureType}{empty},
then i is undefined and t does not occur in a.
\end{itemize}
The structure a does not need to be sorted, and the complexity is expected
to be linear in the size of the structure, unless otherwise specified by
the actual type.}
\Remarks{No copy of a is made: if b is not \asfunc{LinearStructureType}{empty}, then its data is
shared with a. This function allows all the occurences of t to be found
successively in a structure, as in the example below.}
\begin{asex}
If {\tt l1} is the list of \astype{MachineInteger} [1,6,2,5,3,7,2,4],
then {\tt (l2, n) := find(2, l1)} sets {\tt l2} to [2,5,3,7,2,4]
and {\tt n} to 3, the further call {\tt (l3, n) := find(2, rest l2)}
sets {\tt l3} to [2,4] and {\tt n} to 4, and the further call
{\tt (l4, n) := find(2, rest l3)} sets {\tt l4} to
\asfunc{LinearStructureType}{empty}.
\end{asex}
#endif
	}
	generator: % -> Generator T;
#if ALDOC
\aspage{generator}
\Usage{ for x in a repeat \{ \dots \}\\ for x in \name~a repeat \{ \dots \} }
\Signature{\%}{\astype{Generator} T}
\Params{ {\em a} & \% & a finite linear structure\\ }
\Descr{This function allows a structure to be iterated independently of its
representation. This generator yields the elements of a in succession.}
\begin{asex}
The following code computes the sum of all the elements
of an array of machine integers:
\begin{ttyout}
sum(a:Array MachineInteger, n:MachineInteger):MachineInteger == {
    s:MachineInteger := 0;
    for x in a repeat s := s + x;
    s;
}
\end{ttyout}
\end{asex}
#endif
	map: (T -> T) -> % -> %;
	map!: (T -> T) -> % -> %;
#if ALDOC
\aspage{map}
\astarget{\name!}
\Usage{\name~f\\\name!~f\\\name(f)(a)\\\name!(f)(a)}
\Signature{(T $\to$ T) $\to$ \%}{\%}
\Params{
{\em f} & T $\to$ T & a map\\
{\em a} & \% & a finite linear structure\\
}
\Retval{\name(f)(a) returns the new structure {\tt [f(x) for x in a]}, while
\name(f) returns the mapping $a \to$ {\tt [f(x) for x in a]}. In both cases,
\name!~does not make a copy of the structure a but modifies it in place.}
#endif
	if T has PrimitiveType then {
		PrimitiveType;
		member?: (T, %) -> Boolean;
#if ALDOC
\aspage{member?}
\Usage{\name(t, a)}
\Signature{(T, \%)}{\astype{Boolean}}
\Params{
{\em t} & T & the value to search for\\
{\em a} & \% & a finite linear structure\\
}
\Retval{Returns \true if t is a member of a, \false otherwise.}
#endif
	}
	default {
		if T has PrimitiveType then {
			(a:%) = (b:%):Boolean == {
				import from Z, T;
				#a ~= #b => false;
				for x in a for y in b repeat
					x ~= y => return false;
				true;
			}

			member?(t:T, a:%):Boolean == {
				(b, n) := find(t, a);
				~empty? b;
			}

			equal?(a:%, b:%, n:Z):Boolean == {
				import from T;
				for x in a for y in b for i in 1..n repeat
					x ~= y => return false;
				true;
			}

		}

		if T has HashType then {
			hash(a:%):Z == {
				import from T;
				h:Z := 0;
				for x in a for i in 1.. repeat
					h := h + i * hash x;
				h;
			}
		}

		if T has SerializableType then {
			(p:BinaryWriter) << (a:%):BinaryWriter == {
				import from Z, T;
				p := p << #a;		-- write size first
				for t in a repeat p := p << t;
				p;
			}
		}
	}
}
