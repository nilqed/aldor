------------------------------ sit_maple.as ------------------------------
--
-- Basic Maple - Aldor Interface
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "algebra"

macro {
	TREE	== ExpressionTree;
	PTREE	== Partial TREE;
}


Maple:with {
	input: % -> TextWriter;
	maple: (debug?:Boolean == false) -> %;
	run: % -> PTREE;
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
