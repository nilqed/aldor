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
------------------------------- sit_abmon.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{AbelianMonoid}
\History{Manuel Bronstein}{24/3/99}{created}
\Usage{\this: Category}
\Descr{\this~is the category of commutative monoids.}
\begin{exports}
\category{\astype{SumitType}}\\
\asexp{$0$}: & \% & zero\\
\asexp{$+$}: & (\%, \%) $\to$ \% & sum\\
\asexp{$*$}: & (\astype{Integer}, \%) $\to$ \% & product by an integer\\
\asexp{add!}: & (\%, \%) $\to$ \% & In--place sum\\
\asexp{zero?}: & \% $\to$ \astype{Boolean} & test for $0$\\
\end{exports}
#endif

define AbelianMonoid: Category == SumitType with {
	0: %;
#if ALDOC
\aspage{$0$}
\Usage{\name}
\Signature{}{\%}
\Retval{Returns the constant $0$.}
#endif
        +: (%, %) -> %;
#if ALDOC
\aspage{+}
\Usage{$x \name y$}
\Signature{(\%,\%)}{\%}
\Params{{\em x,y} & \% & elements of the monoid\\ }
\Retval{Returns the sum $x+y$.}
#endif
	*: (Integer, %) -> %;
#if ALDOC
\aspage{$*$}
\Usage{n \name~x}
\Signature{(Integer, \%)}{\%}
\Params{
{\em n} & Integer & An integer\\
{\em x} & \% & An element of the monoid to be multiplied by n\\
}
\Retval{Returns the product $n x$.}
#endif
	add!: (%, %) -> %;
#if ALDOC
\aspage{add!}
\Usage{\name(x, y)}
\Signature{(\%, \%)}{\%}
\Params{
{\em x} & \% & An element of the monoid (to be destroyed)\\
{\em y} & \% & An element of the monoid to be added to x\\
}
\Retval{Returns the sum $x + y$, where the storage used by x is allowed
to be destroyed or reused, so x is lost after this call.}
\Remarks{This function may cause x to be destroyed, so do not use it unless
x has been locally allocated, and is guaranteed not to share space
with other elements. Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
#endif
	zero?: % -> Boolean;
#if ALDOC
\aspage{zero?}
\Usage{\name~x}
\Signature{\%}{\astype{Boolean}}
\Params{{\em x} & \% & an element of the monoid\\ }
\Retval{Returns the result of $x = 0$ using the semantics of $=$ of the monoid.}
#endif
	default {
		local copy?:Boolean	== % has CopyableType;
		zero?(x:%):Boolean	== x = 0;

		add!(a:%, b:%):% == {
			zero? a => { copy?=>copy(b)$(% pretend CopyableType);b }
			a + b;
		}
	}
}
