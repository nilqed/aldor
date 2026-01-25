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
---------------------------- sit_shell.as -----------------------------
--
-- Shells, i.e. read-eval loops.
--
-- Copyright (c) Manuel Bronstein 1996
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1996-97
-----------------------------------------------------------------------------

#include "sumit"

macro {
	Z	== MachineInteger;
	TX	== TextWriter;
	TAB	== SymbolTable;
	NL	== newline;
}

#if ALDOC
\thistype{Shell}
\History{Manuel Bronstein}{10/01/96}{created}
\Usage{import from \this(P, R, E)}
\Params{
P & \astype{Parser} & A parser type for the input\\
R & \astype{PartialRing} & Resulting type of the evaluation\\
E & \astype{Evaluator} R & An interpreter with target type R\\
}
\Descr{\this(P, R, E) provides a basic read-eval-loop that converts its input
to expressions of type R.}
\begin{exports}
\asexp{banner}: & (TW, \astype{String}) $\to$ TW & Print a banner\\
\asexp{shell!}: &
(P, TW, TW, \astype{SymbolTable} R, \astype{Boolean}, \astype{String}) $\to$ Z &
Read-eval loop\\
\end{exports}
\begin{aswhere}
TW &==& \astype{TextWriter}\\
Z &==& \astype{MachineInteger}\\
\end{aswhere}
#endif

Shell(P:Parser, R:PartialRing, E:Evaluator R): with {
	banner: (TX, String) -> TX;
#if ALDOC
\aspage{banner}
\Usage{\name(p, s)}
\Signature{(\astype{TextWriter}, \astype{String})}{\astype{TextWriter}}
\Params{
{\em p} & \astype{TextWriter} & The port to write to\\
{\em s} & \astype{String} & A name to center in the banner\\
}
\Descr{Writes the default \sumit~banner to the port p.}
\Remarks{The string s is automatically centered in the banner. In order
for the banner to look ok, it must have a maximum of 33 characters.}
\begin{asex}
\begin{ttyout}
banner(print, "B E R N I N A");
\end{ttyout}
prints the following banner:
\begin{verbatim}
                                                          /\    
      -----  it                                          /| \    
      \                   B E R N I N A                 / |  \    
       \                                               |   \  \   
       /                 A Sum^it server               |    |  \  
      /                                                /     \  \ 
      -----                                           /      |   \
                                                     /       /    \


\end{verbatim}
\end{asex}
#endif
	shell!: (P, TX, TX, TAB R, Boolean, String) -> Z;
#if ALDOC
\aspage{shell!}
\Usage{\name(r, $p_1, p_2$, t, verbose?, s)}
\Signature{(P, \astype{TextWriter}, \astype{TextWriter}, \astype{SymbolTable} R,
\astype{Boolean}, \astype{String})}{\astype{MachineInteger}}
\Params{
{\em r} & P & A parser\\
$p_1,p_2$ & \astype{TextWriter} & The ports to write to\\
{\em t} & \astype{SymbolTable} R & The initial symbol table\\
{\em verbose?} & \astype{Boolean} & Select verbose or quiet mode\\
{\em s} & \astype{String} & A string to write after processing commands\\
}
\Descr{Starts a read-eval loop which takes its input from r and writes
its output to $p_1$ or $p_2$. Mathematical output generated by user commands
is written to $p_1$, while prompts and execution times are written to $p_2$.
if verbose? is false (quiet mode), nothing is printed to $p_2$ and no
prompts or execution times are communicated. If s is not empty, then
it is sent to $p_1$ after each command is executed.
The table t contains the initial environment, and can be modified by the loop.
Returns an integer $n = b_1 b_0$ where $b_0$ is 1 if a syntax error occured,
0 otherwise, and $b_1$ is 1 if any other error occured, 0 otherwise.}
#endif
} == add {
	local prompt(p:TX, n:Z):TX == {
		import from Character, WriterManipulator, String;
		p << newline << n << " --> " << flush;
	}

	local err1(p:TX, msg:String, verbose?:Boolean):() == {
		import from WriterManipulator, String;
		if verbose? then p << "*** " << msg << " ***" << endnl;
	}

-- title is automatically centered in a 33-character field
	banner(p:TX, title:String):TX == {
		import from Z, Character, WriterManipulator;
		n := max(0, 33 - #title);	-- total # of spaces to add
		n2 := n quo 2;
		left := new(n2, space);
		right := new(n - n2, space);
		p << NL;
p << "                                                          /\    " << NL;
p << "      -----  it                                          /| \    " << NL;
p << "      \         "  << left << title << right << "       / |  \    " << NL;
p << "       \                                               |   \  \   " << NL;
p << "       /                 A Sum^it server               |    |  \  " << NL;
p << "      /                                                /     \  \ " << NL;
p << "      -----                                           /      |   \" << NL;
p << "                   Use ^D to terminate session       /       /    \"<< NL;
		p << NL << endnl;
	}

	-- return true if an error has occured
	shell!(pin:P,pout:TX,ptime:TX,t:TAB R,verb?:Boolean,done:String):Z == {
		import from Z,String, WriterManipulator, Partial ExpressionTree;
		err:Z := 0;
		count:Z := 1;
		TRACE("shell::shell!: err = ", err);
		TRACE("shell::shell!: count = ", count);
		if verb? then prompt(ptime, count);
		done? := ~empty? done;
		while ~eof? pin repeat {
			if failed?(tree := parse! pin) then {
				err := err \/ 1;
				err1(pout, "syntax error", verb? and ~eof? pin);
			}
			else {
				if process(pout, ptime, retract tree, t, verb?)
							then err := err \/ 2;
				else if done? then pout << done << endnl;
			}
			count := next count;
			if verb? then prompt(ptime, count);
		}
		if verb? then ptime << endnl;
		err;
	}

	-- return true if an error has occured
	local process(p:TX, ptime:TX, tree:ExpressionTree, t:TAB R,
		verbose?:Boolean):Boolean == {
			import from E, R, Partial R, Timer, String;
			import from WriterManipulator;
			clock := timer();
			start! clock;
			result := eval!(p, tree, t);
			msecs := stop! clock;
			if (err? := failed? result) then
				err1(p, "failed to evaluate", true);
			if verbose? then {
				ptime := printTime(ptime, msecs);
				ptime := printTime(ptime << " (gc = ",gc clock);
				ptime << ")" << endnl;
			}
			err?;
	}

	local printTime(p:TX, time:Z):TX == {
		import from String;
		assert(time >= 0);
		(hours, time) := divide(time, 3600000);
		p << hours << ":";
		(mins, time) := divide(time, 60000);
		if mins < 10 then p << "0";
		p << mins << ":";
		(secs, time) := divide(time, 1000);
		if secs < 10 then p << "0";
		p << secs << ".";
		if time < 100 then p << "0";
		if time < 10 then p << "0";
		p << time;
	}
}
