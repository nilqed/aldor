----------------------- sit_parser.as ---------------------------------
--
-- Parser Category
--
-- Copyright (c) Niklaus Mannhart 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "algebra"


define Parser: Category == with {
	eof?:	      % -> Boolean;
	lastError:    % -> MachineInteger;
	parse!:       % -> Partial ExpressionTree;
};


define ParserReader: Category == Parser with {
	parser:	TextReader -> %;
}
