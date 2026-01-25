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
---------------------------- sal_char.as ---------------------------------
--
-- This file adds I/O and serialization to Character
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro Z == MachineInteger;

#if ALDOC
\thistype{Character}
\History{Manuel Bronstein}{1/10/98}{created}
\Usage{import from \this}
\Descr{\this~implements machine characters.}
\begin{exports}
\category{\astype{HashType}}\\
\category{\astype{InputType}}\\
\category{\astype{OutputType}}\\
\category{\astype{SerializableType}}\\
\asexp{char}: & \astype{MachineInteger} $\to$ \% & create a character\\
\asexp{digit?}: & \% $\to$ \astype{Boolean} & test for a decimal digit\\
\asexp{eof}: & \% & end--of--file character\\
\asexp{letter?}: & \% $\to$ \astype{Boolean} & test for a letter\\
\asexp{lower}: & \% $\to$ \% & convert to lower case\\
\asexp{newline}: & \% & newline character\\
\asexp{null}: & \% & null character\\
\asexp{ord}: & \% $\to$ \astype{MachineInteger} & character code\\
\asexp{space?}: & \% $\to$ \astype{Boolean} & test for a blank space\\
\asexp{tab}: & \% & tab character\\
\asexp{upper}: & \% $\to$ \% & convert to upper case\\
\end{exports}

\aspage{char,ord}
\astarget{char}
\astarget{ord}
\Usage{char~n\\ord~c}
\Signatures{
char: & \astype{MachineInteger} $\to$ \%\\
ord: & \% $\to$ \astype{MachineInteger}\\
}
\Params{
{\em n} & \astype{MachineInteger} & a character code\\
{\em c} & \% & a character\\
}
\Retval{char(n) returns the character whose code is n, while ord(c) returns
the code corresponding to the character c.}

\aspage{digit?,letter?,space?}
\astarget{digit?}
\astarget{letter?}
\astarget{space?}
\Usage{digit?~c\\letter?~c\\space?~c}
\Signature{\%}{\astype{Boolean}}
\Params{ {\em c} & \% & a character\\ }
\Retval{digit?(c) returns \true if c is in the range '0'--'9', \false otherwise,
while letter?(c) returns \true if c is in the range 'a'--'z' or the range
'A'--'Z', \false otherwise and space?(c) returns \true if c is a blank space,
\ie a space or a tab, \false otherwise.}

\aspage{eof,newline,null,tab}
\astarget{eof}
\astarget{newline}
\astarget{null}
\astarget{tab}
\Usage{eof\\ newline\\ null\\ tab}
\Signature{}{\%}
\Retval{eof is the end--of--file character, newline is the newline character,
null is the 0-character (used to terminate strings) and tab is the
tab character.}

\aspage{lower,upper}
\astarget{lower}
\astarget{upper}
\Usage{lower~c\\upper~c}
\Signature{\%}{\%}
\Params{ {\em c} & \% & a character\\ }
\Retval{lower(c) and upper(c) return c converted to lower, respectively upper,
case.}
#endif
-- characters are read and written the same way, whether in text or binary
extend Character:Join(SerializableType, InputType, OutputType, HashType)== add {
	import from Byte;
	<< (p:TextReader):%			== read! p;
	<< (p:BinaryReader):%			== read!(p)::%;
	(p:TextWriter) << (x:%):TextWriter	== { write!(x, p); p }
	(p:BinaryWriter) << (x:%):BinaryWriter	== { write!(x::Byte, p); p }
	hash(x:%):MachineInteger		== ord x;
}

