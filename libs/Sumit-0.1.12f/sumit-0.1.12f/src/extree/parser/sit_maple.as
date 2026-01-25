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
------------------------------ sit_maple.as ------------------------------
--
-- Basic Maple - Aldor Interface
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	TREE	== ExpressionTree;
	PTREE	== Partial TREE;
}

#if ALDOC
\thistype{Maple}
\History{Manuel Bronstein}{15/04/98}{created}
\Usage{import from \this}
\Descr{\this~provides utilities that allow its clients to batch \maple
sessions and recover the output.}
\begin{exports}
\asexp{input}:
& \% $\to$ \astype{TextWriter} & Input stream of the maple session\\
\asexp{maple}: & () $\to$ \% & Create a maple session\\
\asexp{run}:
& \% $\to$ \astype{Partial} \astype{ExpressionTree} & Run a maple session\\
\end{exports}
#endif

Maple:with {
	input: % -> TextWriter;
#if ALDOC
\aspage{input}
\Usage{\name~m}
\Signature{\%}{\astype{TextWriter}}
\Params{m & \% & A maple session\\}
\Retval{Returns the input stream for the maple session.}
\Remarks{Use that stream to send sequences of valid maple commands, making
sure that all the commands are terminated with `:` in order to avoid any
printing from \maple. Do not use any of \maple's printing functions. Note
that the system maple is not started until 'run' is called.}
#endif
	maple: (debug?:Boolean == false) -> %;
#if ALDOC
\aspage{maple}
\Usage{\name()}
\Signature{()}{\%}
\Descr{Creates a maple session, by associating unique communications channels
to and from that session.}
\Remarks{The maple input and output files used for communication are located
in the /tmp directory and are deleted after the session is run, unless
the call {\tt maple(true)} is used, in which case they remain and can
be inspected. Note that the system maple is not started until 'run' is called.}
#endif
	run: % -> PTREE;
#if ALDOC
\aspage{run}
\Usage{\name~m}
\Signature{\%}{\astype{Partial} \astype{ExpressionTree}}
\Params{m & \% & A maple session\\}
\Descr{Launches the system maple and executes all the commands that were
sent to the input stream of the session. Returns the expression tree
corresponding to the value returned by the last maple command executed.}
\begin{asex}
This examples shows how to call \maple to compute the integral
of the $\sth{5}$ Legendre polynomial:
\begin{ttyout}
import from Integer, Maple, ExpressionTree, Partial ExpressionTree;

n := 5;
-- create a session (maple is not launched but a unique link is created)
mapl := maple();

-- send the maple code to compute the integral of the n-th legendre poly
-- note that all the maple commands are terminated with ":"
-- so that they do not generate any output
-- here again, nothing happens, the commands are only stored
input(mapl) << "with(orthopoly): p := P(" << n << ", x): int(p, x):";

-- now launch maple and recover the result of the last command ("int")
tree := run mapl;

failed? tree => error "Unable to parse Maple's output";
retract tree;
\end{ttyout}
Running the above code produces the following expression tree:
\begin{asoutput}
(+
(- (* (/ 21 16) (\^{} x 6)) (* (/ 35 16) (\^{} x 4)))
(* (/ 15 16) (\^{} x 2))
)
\end{asoutput}
\end{asex}
#endif
} == add {
	Rep == Record(nam:String, inp:File, del?:Boolean);
	import from Rep;

	local name(m:%):String		== rep(m).nam;
	local file(m:%):File		== rep(m).inp;
	local delete?(m:%):Boolean	== rep(m).del?;
	local outputName(m:%):String	== name(m) + ".out";
	input(m:%):TextWriter	== { import from File; file(m)::TextWriter; }

	maple(debug?:Boolean):% == {
		import from Character, File, MachineInteger;
		TRACE("maple::maple(): debug? = ", debug?);
		s := uniqueName "/tmp/sumitMaple";
		TRACE("maple::maple(): s = ", s);
		m := per [s, open(s,fileWrite + fileText), ~debug?];
		-- Maple hack: _sumitMapleVersion is 1 for V.4, 0 for V.5
		input(m) << "1:1:_sumitMapleVersion := length(_"_"):" <<newline;
		m;
	}

	run(m:%):PTREE == {
		import from Character, String, File, MachineInteger;
		import from TextReader, InfixExpressionParser;
		import { system: Pointer -> () } from Foreign C;
		TRACE("maple::run: ", name m);
		-- Maple hack: _sumitMapleVersion is 1 for V.4, 0 for V.5
		input(m) << "if _sumitMapleVersion = 0 then ";
		input(m) << "printf(`%a\n`, eval(`%`)) else ";
		input(m) << "printf(`%a\n`, eval(`_"`)) fi: done:" << newline;
		close! file m;
		sout := outputName m;
		cmd := "maple -q < " + name(m) + " > " + sout;
		TRACE("maple::run: cmd = ", cmd);
		system pointer cmd;
		out := open(sout, fileRead + fileText);
		ans := parse! parser(out::TextReader);
		if delete? m then {
			remove name m;
			remove sout;
		}
		ans;
	}
}
