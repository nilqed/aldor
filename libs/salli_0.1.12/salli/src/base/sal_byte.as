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
---------------------------- sal_byte.as ---------------------------------
--
-- This file adds I/O and serialization to Byte
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

#if ALDOC
\thistype{Byte}
\History{Manuel Bronstein}{8/12/98}{created}
\Usage{import from \this}
\Descr{\this~implements machine bytes.}
\begin{exports}
\category{\astype{HashType}}\\
\category{\astype{InputType}}\\
\category{\astype{OutputType}}\\
\category{\astype{SerializableType}}\\
\asexp{coerce}: & \% $\to$ \astype{MachineInteger} & conversion to an integer\\
\asexp{coerce}: & \% $\to$ \astype{Character} & conversion to a character\\
\asexp{coerce}: & \astype{Character} $\to$ \% & conversion from a character\\
\asexp{eof}: & \% & end--of--file marker\\
\asexp{lowByte}: & \astype{MachineInteger} $\to$ \% & low--byte of an integer\\
\end{exports}

\aspage{coerce}
\Usage{b::\astype{MachineInteger}\\ b::\astype{Character}\\ c::\%}
\Signatures{
\name: & \% $\to$ \astype{MachineInteger}\\
\name: & \% $\to$ \astype{Character}\\
\name: & \astype{Character} $\to$ \%\\
}
\Params{
{\em b} & \% & a byte\\
{\em c} & \astype{Character} & a character\\
}
\Retval{b::\astype{MachineInteger} and b::\astype{Character} return b
converted to an integer and a character respectively,
while c::\% returns c converted to a byte.}

\aspage{eof}
\Usage{\name}
\Signature{}{\%}
\Retval{eof is the end--of--file marker.}

\aspage{lowByte}
\Usage{\name~n}
\Signature{\astype{MachineInteger}}{\%}
\Params{ {\em n} & \astype{MachineInteger} & an integer\\ }
\Retval{Returns the low--byte of n.}
#endif
-- bytes are read and written the same way, whether in text or binary
-- the extensions to InputType and OutputType are done later after machine-int
extend Byte:Join(HashType, SerializableType) == add {
	<< (p:BinaryReader):%			== read! p;
	(p:BinaryWriter) << (x:%):BinaryWriter	== { write!(x, p); p }
	hash(x:%):MachineInteger		== x::MachineInteger;
}


-- read/write T/F in text, 1/0 in binary (1 byte)
extend Boolean:Join(SerializableType, InputType, OutputType) == add {
	import from Byte, Character, MachineInteger;

	(p:TextWriter) << (x:%):TextWriter	== p << char({ x => 84; 70 });
	(p:BinaryWriter) << (x:%):BinaryWriter	== p << lowByte({ x => 1; 0 });

	<< (p:TextReader):% == {
		local c:Character;
		(c := << p) = char 70 => false;
		assert(c = char 84);
		true;
	}

	<< (p:BinaryReader):% == {
		zero?(n := (<< p)@Byte :: MachineInteger) => false;
		assert(n = 1);
		true;
	}
}

