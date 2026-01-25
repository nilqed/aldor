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
---------------------------- sal_pointer.as ------------------------------------
--
-- Pointers
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro Z == MachineInteger;

#if ALDOC
\thistype{Pointer}
\History{Manuel Bronstein}{28/9/98}{created}
\Usage{import from \this}
\Descr{\this~implements machine pointers.}
\begin{exports}
\category{\astype{HashType}}\\
\category{\astype{InputType}}\\
\category{\astype{OutputType}}\\
\category{\astype{SerializableType}}\\
{\tt coerce}: & \% $\to$ \astype{MachineInteger} & conversion to an integer\\
{\tt coerce}: & \astype{MachineInteger} $\to$ \% & conversion from an integer\\
\asexp{nil}: & \% & the nil pointer\\
\asexp{nil?}: & \% $\to$ \astype{Boolean} & test for the nil pointer\\
\end{exports}

\aspage{nil}
\astarget{\name?}
\Usage{\name\\ \name?~p}
\Signatures{
\name: & $\to$ \% \\
\name?: & \% $\to$ \astype{Boolean}\\
}
\Params{ {\em p} & \% & a pointer\\ }
\Retval{\name~returns the nil pointer, while \name?(p) returns \true~if
p is the nil pointer, \false otherwise.}
#endif

extend Pointer:Join(HashType, InputType, OutputType, SerializableType) == add {
	import from Z;
	<< (p:BinaryReader):%			== (<< p)@Z :: %;
	(p:BinaryWriter) << (x:%):BinaryWriter	== p << x::Z;
	hash(x:%):Z				== x::Z;

	<< (p:TextReader):% == {
		import from Z, IntegerTypeTools Z;
		local c:Character;
		while space?(c := << p) repeat {};
		c ~= char 48 => 0::%;
		c := << p;
		c ~= char 120 => 0::%;
		scan(p, 16, 0)::%;
	}

	(p:TextWriter) << (x:%):TextWriter == {
		import from Z, IntegerTypeTools Z, Character;
		print(x::Z, 16, p << char 48 << char 120);	-- 0x....
	}
}
