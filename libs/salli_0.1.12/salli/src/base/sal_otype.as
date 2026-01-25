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
----------------------------- sal_otype.as ----------------------------------
--
-- This file defines writable objects
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

#if ALDOC
\thistype{OutputType}
\History{Manuel Bronstein}{28/9/98}{created}
\Usage{\this: Category}
\Descr{\this~is the category of types whose objects can be written onto text
writers.}
\begin{exports}
\asexp{$<<$}: & (\astype{TextWriter}, \%) $\to$ \astype{TextWriter} &
write using text encoding\\
\end{exports}
#endif

define OutputType: Category == with {
	<<: (TextWriter, %) -> TextWriter;
#if ALDOC
\aspage{$<<$}
\Usage{s $<<$ x}
\Signature{(\astype{TextWriter}, \%)}{\astype{TextWriter}}
\Params{
{\em s} & \astype{TextWriter} & an output stream\\
{\em x} & \% & an object of the type\\
}
\Retval{writes x in text format to the stream s
and returns s after the write.}
\begin{asex}
\begin{ttyout}
import from TextWriter, MachineInteger, Character;
stdout << 65 << space;
\end{ttyout}
writes ``65 '' to the standard output stream.
\end{asex}
#endif
}

