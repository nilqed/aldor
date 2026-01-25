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
---------------------------- sal_ckarray.as ----------------------------------
--
-- This file defines arrays with base-translations.
-- Those arrays are 0-indexed and carry-out bound-checking.
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro Z  == MachineInteger;

#if ALDOC
\thistype{CheckingArray}
\History{Manuel Bronstein}{12/04/2000}{created}
\Usage{import from \this~T}
\Params{{\em T} & Type & the type of the array entries\\}
\Descr{\this~provides arrays of entries of type $T$,
$0$-indexed and with bound checking.}
\begin{exports}
\category{\astype{ArrayType}(T, \astype{PrimitiveArray} T)}\\
\end{exports}
\Remarks{The functions \asfunc{ArrayType}{apply}
and \asfunc{LinearStructureType}{set!}
throw the exception \astype{ArrayException} when attempting to access
an array out of its bounds.}
#endif

CheckingArray(T:Type): ArrayType(T, PrimitiveArray T) == Array T add {
	apply(a:%, n:Z, m:Z):% == {
		import from PrimitiveArray T;
		n < 0 or m < n or m >= #a => throw ArrayException;
		array(data(a) + n, next(m - n));
	}

	apply(x:%, n:Z):T == {
		import from PrimitiveArray T;
		n < 0 or n >= #x => throw ArrayException;
		data(x).n;
	}

	set!(x:%, n:Z, y:T):T == {
		import from PrimitiveArray T;
		n < 0 or n >= #x => throw ArrayException;
		data(x).n := y;
	}
}

