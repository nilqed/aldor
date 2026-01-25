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
----------------------------- sal_htype.as ----------------------------------
--
-- This file defines hashable types
--
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 24-06-99
-- Logiciel Salli ©INRIA 1999, dans sa version du 24/06/1999
-----------------------------------------------------------------------------

#include "salli"

#if ALDOC
\thistype{HashType}
\History{Manuel Bronstein}{24/6/99}{created}
\Usage{\this: Category}
\Descr{\this~is the category of types whose objects can be hashed into
machine integers.}
\begin{exports}
\category{\astype{PrimitiveType}}\\
\asexp{hash}: & \% $\to$ \astype{MachineInteger} & hash function\\
\end{exports}
#endif

define HashType: Category == PrimitiveType with {
	hash: % -> MachineInteger;
#if ALDOC
\aspage{hash}
\Usage{\name~x}
\Signature{\%}{\astype{MachineInteger}}
\Params{ {\em x} & \% & an element of the type\\ }
\Retval{Returns a hash--code for x.}
#endif
}

