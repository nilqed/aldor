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
------------------------------- sal_copy.as ----------------------------------
--
-- Types that have a copy function
--
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

#if ALDOC
\thistype{CopyableType}
\History{Manuel Bronstein}{24/3/99}{created}
\Usage{\this: Category}
\Descr{ \this~is the category of types whose objects can be copied.}
\begin{exports}
\asexp{copy:} & \% $\to$ \% & Make a copy\\
\asexp{copy!}: & (\%, \%) $\to$ \% & In-place copy\\
\end{exports}
#endif

define CopyableType: Category == with {
	copy: % -> %;
	copy!: (%, %) -> %;
#if ALDOC
\aspage{copy}
\astarget{\name!}
\Usage{\name~y\\ \name!(x, y)}
\Signatures{
\name: \% $\to$ \%\\
\name!: (\%, \%) $\to$ \%\\
}
\Params{ {\em x,y} & \% & Element of the type\\ }
\Retval{\name(y) returns a copy of y, while
\name!(x, y) returns a copy of y, where the storage used by x is allowed
to be destroyed or reused, so x is lost after this call.}
\Remarks{Use \name~before making in--place operations on a parameter.
The call \name!(x, y) may cause x to be destroyed, so do not use it unless
x has been locally allocated, and is guaranteed not to share space
with other elements. Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
#endif
	default copy!(a:%, b:%):% == copy b;
}
