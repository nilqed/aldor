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
---------------------------- sal_memblk.as ----------------------------------
--
-- This file defines memory blocks, i.e. packed byte-arrays
-- Those arrays are 0-indexed and do not carry out bound-checking.
--
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro {
	A  == PrimitiveMemoryBlock;
	Z  == MachineInteger;
}

#if ALDOC
\thistype{MemoryBlock}
\History{Manuel Bronstein}{24/5/2000}{created}
\Usage{import from \this}
\Descr{\this~provides packed arrays of bytes,
$0$-indexed and without bound checking (the debug version
of \salli provides bound--checking for memory blocks).}
\begin{exports}
\category{\astype{ArrayType}(\astype{Byte}, \astype{PrimitiveMemoryBlock})}\\
\end{exports}
#endif

MemoryBlock: ArrayType(Byte, A) == add {
	Rep == Record(size:Z, arr: A);
	import from A;

	#(x:%):Z			== { import from Rep; rep(x).size }
	data(x:%):A			== { import from Rep; rep(x).arr }
	array(p:A, n:Z):%		== { import from Rep; per [n, p] }
	empty:%				== { import from Z; array(empty, 0) }
	firstIndex:Z			== 0;

	resize!(x:%, n:Z):% == {
		assert(n >= 0);
		a := data x;
		if n > #x then a := resize!(a, #x, n);
		reset!(x, n, a);
	}

	local reset!(x:%, n:Z, a:A):% == {
		import from Rep;
		rep(x).size := n;
		rep(x).arr := a;
		x;
	}

	copy!(b:%, a:%):% == {
		import from Z;
		q:A := {
			(n := #a) > #b => new n;
			data b;
		}
		p := data a;		-- optimizes code generation
		for i in 0..prev n repeat q.i := p.i;
		reset!(b, n, q);
	}
}

