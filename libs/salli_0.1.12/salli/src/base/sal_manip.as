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
---------------------------- sal_manip.as ---------------------------------
--
-- This file defines output stream manipulators
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro {
	Ch == Character;
	Z == MachineInteger;
}

#if ALDOC
\thistype{WriterManipulator}
\History{Manuel Bronstein}{26/10/98}{created}
\Usage{import from \this}
\Descr{\this~provides manipulators for text or binary writers.}
\begin{exports}
\asexp{$<<$}: & (\astype{BinaryWriter}, \%) $\to$ \astype{BinaryWriter} &
manipulate a binary writer\\
\asexp{endnl}: & \% & send a newline and flush the stream\\
\asexp{flush}: & \% & flush the stream\\
\end{exports}
#endif

WriterManipulator: OutputType with {
	<<: (BinaryWriter, %) -> BinaryWriter;
#if ALDOC
\aspage{$<<$}
\Usage{out $<<$ x}
\Signature{(\astype{BinaryWriter}, \%)}{\astype{BinaryWriter}}
\Params{
{\em out} & \astype{BinaryWriter} & an output stream\\
{\em x} & \% & a manipulator\\
}
\Retval{out $<<$ x takes the action given by x on the stream out
and returns the stream after the action.}
#endif
	endnl: %;
#if ALDOC
\aspage{endnl}
\Usage{\name}
\Signature{}{\%}
\Descr{Sending \name~to a text or binary writer causes a
\asfunc{Character}{newline}
to be sent to the stream and then the stream to be flushed,
so {\tt s $<<$ endnl} is equivalent to {\tt flush!(s $<<$ newline)}.}
#endif
	flush: %;
#if ALDOC
\aspage{flush}
\Usage{\name}
\Signature{}{\%}
\Descr{Sending \name~to a text or binary writer causes the stream to
be flushed, so {\tt s $<<$ flush} is equivalent to {\tt flush!(s)}.
Has no effect on unbuffered streams, such as \asfunc{BinaryWriter}{stderr}.}
#endif
} == add {
	Rep == Ch;
	import from Rep, Z;

	flush:%			== per char 0;
	endnl:%			== per char 1;
	local int(x:%):Z	== ord rep x;

	(s:BinaryWriter) << (x:%):BinaryWriter == {
		import from Byte;
		zero?(n := int x) => flush! s;
		n = 1 => { write!(newline::Byte, s); flush! s; }
		never;
	}

	(s:TextWriter) << (x:%):TextWriter == {
		zero?(n := int x) => flush! s;
		n = 1 => { write!(newline, s); flush! s; }
		never;
	}
}
