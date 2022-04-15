---------------------------- sit_shell.as -----------------------------
--
-- Shells, i.e. read-eval loops.
--
-- Copyright (c) Manuel Bronstein 1996
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1996-97
-----------------------------------------------------------------------------

#include "algebra"

macro {
	B	== Boolean;
	Z	== MachineInteger;
	TX	== TextWriter;
	TAB	== SymbolTable;
	NL	== newline;
}


Shell(P:Parser, R:PartialRing, E:Evaluator R): with {
	center: (TX, String) -> TX;
	shell!: (P, TX, TX, TAB R, B, B, String) -> Z;
} == add {
	local prompt(p:TX, n:Z):TX == {
		import from Character, WriterManipulator, String;
		p << newline << n << " --> " << flush;
	}

	local err1(p:TX, msg:String, verbose?:B):() == {
		import from WriterManipulator, String;
		if verbose? then p << "*** " << msg << " ***" << endnl;
	}

	-- title is automatically centered in a 66-character field
	center(p:TX, title:String):TX == {
		import from Z, Character;
		n := max(0, 66 - #title);	-- total # of spaces to add
		n2 := n quo 2;
		left := new(n2, space);
		right := new(n - n2, space);
		p << left << title << right << NL;
	}

	-- return true if an error has occured
	shell!(pin:P,pout:TX,ptime:TX,t:TAB R,verb?:B,time?:B,done:String):Z=={
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
				if process(pout, ptime, retract tree, t, verb?,
						time?) then err := err \/ 2;
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
		verbose?:B, time?:B):B == {
			import from Z, E, R, Partial R, Timer, String;
			import from Character, WriterManipulator;
			clock := timer();
			start! clock;
			result := eval!(p, tree, t);
			msecs := stop! clock;
			if (err? := failed? result) then
				err1(p, "failed to evaluate", true);
			if time? then p << msecs << newline << gc clock <<endnl;
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
