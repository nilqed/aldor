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
----------------------- sit_parser.as ---------------------------------
--
-- Parser Category
--
-- Copyright (c) Niklaus Mannhart 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{Parser}
\History{Niklaus Mannhart}{25/03/96}{created}
\History{Manuel Bronstein}{25/09/96}{turned into a category}
\Usage{\this: Category}
\Descr{\this~is the category for parser objects.}
\begin{exports}
\asexp{eof?}: & \% $\to$ \astype{Boolean} & Check for end of input\\
\asexp{lastError}:
& \% $\to$ \astype{MachineInteger} & Code for last parsing error\\
\asexp{parse!}:
& \% $\to$ \astype{Partial} \astype{ExpressionTree} & Parse one expression\\
\end{exports}
#endif

Parser: Category == with {
	eof?:	      % -> Boolean;
#if ALDOC
\aspage{eof?}
\Usage{\name~p}
\Signature{\%}{\astype{Boolean}}
\Params{ {\em p} & \% & A parser \\ }
\Retval{Returns \true~if the input is finished, \false~otherwise.}
#endif
	lastError:    % -> MachineInteger;
#if ALDOC
\aspage{lastError}
\Usage{\name~p}
\Signature{\%}{\astype{MachineInteger}}
\Params{ {\em p} & \% & A parser \\ }
\Retval{Returns the code for the last parsing error.}
#endif
	parse!:       % -> Partial ExpressionTree;
#if ALDOC
\aspage{parse!}
\Usage{\name~p}
\Signature{\%}{\astype{Partial} \astype{ExpressionTree}}
\Params{ {\em p} & \% & A parser \\ }
\Retval{Returns either an expression tree for the next parsed expression, or
\failed in case of error or end of input.}
\seealso{lastError(\%)}
#endif
};

#if ALDOC
\thistype{ParserReader}
\History{Niklaus Mannhart}{25/03/96}{created}
\History{Manuel Bronstein}{25/09/96}{turned into a category}
\Usage{\this: Category}
\Descr{\this~is the category for parser objects that parse text readers.}
\begin{exports}
\asexp{parser}: & \astype{TextReader} $\to$ \% & Create a parser\\
\end{exports}
#endif

ParserReader: Category == Parser with {
	parser:	TextReader -> %;
#if ALDOC
\aspage{parser}
\Usage{\name~r}
\Signature{\astype{TextReader}}{\%}
\Params{ {\em r} & \astype{TextReader} & The input stream to parse\\ }
\Retval{Returns a parser that takes its input on r.}
#endif
}
