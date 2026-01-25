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
----------------------- sit_lspexpr.as ---------------------------------
--
-- Lisp expression parser
--
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
--
-- grammar: (EBNF notation)
--   Expr       := Leaf | "(" Prefix ")" | "(" List ")"
--   Prefix     := op Expr List
--   List	:= "" | Expr List
-----------------------------------------------------------------------------

#include "sumit"
#include "uid"
#include "tokens"

macro {
	SI	== MachineInteger;
	OP	== ExpressionTreeOperator;
	PTREE	== Partial ExpressionTree;
	TEXT	== TextReader;
}

#if ALDOC
\thistype{LispExpressionParser}
\History{Manuel Bronstein}{25/09/96}{created}
\Usage{import from \this}
\Descr{\this~implements lisp expression parsers.}
\begin{exports}
\category{\astype{ParserReader}}\\
\end{exports}
#endif
 
LispExpressionParser: ParserReader == add {
	macro {
		Rep       == Record(sreader: TEXT, errorCode: SI);
		ExprList  == List ExpressionTree;	
	}
	
	import from SI, Rep;

	parser(reader:TEXT):%	== per [reader, 0];
	eof?(p:%):Boolean		== lastError p = PARSER__EOF;
	lastError(p:%):SI		== rep(p).errorCode;
	local reader(p:%):TEXT	== rep(p).sreader;
	local eof?(t:Token):Boolean	== special? t and (special t =TOK__EOF);
	local setError!(p:%, n:SI):%	== { rep(p).errorCode := n; p; }

	local printOperator(t: Token): () == {
		import from TextWriter, String;
		id := uniqueId$(operator t);
		id = UID__PLUS => stderr << "+"; 
		id = UID__MINUS => stderr << "-";
		id = UID__TIMES => stderr << "*";
		id = UID__DIVIDE => stderr << "/";
		id = UID__EXPT => stderr << "^";
		stderr << "ups ???";
	}
	
	local nextToken!(r:%):Token == {
		import from TEXT, Scanner;
		ctoken := scan! reader r;
#if TRACE
		import from TextWriter, Character, String;
                if eoexpr? ctoken then stderr << "eoexpr";
                else if eof? ctoken then stderr << "eof";
                else if operator? ctoken then {
                        if assign? ctoken then stderr << ":="
                        else printOperator (ctoken);
                }
                else if leaf? ctoken then stderr << "leaf";
                else if special? ctoken then {
                        stderr << "special";
                        if comma? ctoken then stderr << ",";
                        else if leftParen? ctoken then stderr << "(";
                        else if rightParen? ctoken then stderr << ")";
                }
                else if prefix? ctoken then stderr << "prefix";
                else stderr << "????";
                stderr << newline;
#endif
		ctoken;
	}
				
	local leftParen? (t:Token):Boolean == {
		assert(special? t);
		special t = TOK__LPAREN;
	}
		
	local rightParen? (t:Token):Boolean == {
		assert(special? t);
		special t = TOK__RPAREN;
	}
	
	local leftBracket? (t:Token):Boolean ==  {
		assert(special? t);
		special t = TOK__LBRACKET;
	}
	
	local rightBracket? (t:Token):Boolean == {
		assert(special? t);
		special t = TOK__RBRACKET;
	}
		
	local prefix? (t:Token):Boolean == {
		assert(operator? t);
		uniqueId$(operator t) = UID__PREFIX;
	}	

	local prefix!(parser:%, op:OP):PTREE == {
		import from Token, ExpressionTree, ExprList;
		failed?(uexpr := parse! parser) => return failed;
		args:ExprList := [retract uexpr];
		repeat {
			ctoken := nextToken! parser;
			special?(ctoken) and rightParen?(ctoken) =>
				return [op reverse! args];
			failed?(uexpr := parse!(parser, ctoken)) =>
				return failed;
			args := cons(retract uexpr, args);
		}
		never;
	}

	local list!(parser:%, ctoken:Token):PTREE == {
		import from Token, ExpressionTree, ExprList;
		args:ExprList := empty;
		repeat {
			special?(ctoken) and rightParen?(ctoken) =>
				return [ExpressionTreeLispList reverse! args];
			failed?(uexpr := parse!(parser, ctoken)) =>
				return failed;
			args := cons(retract uexpr, args);
			ctoken := nextToken! parser;
		}
		never;
	}

	parse!(parser:%):PTREE == {
		ctoken := nextToken! parser;
		parse!(parser, ctoken);
	}

	local parse!(parser:%, ctoken:Token):PTREE == {
		import from Boolean, ExpressionTreeLeaf, ExpressionTree;
		eof? ctoken => { setError!(parser, PARSER__EOF); failed; }
		setError!(parser, PARSER__NOERROR);
		leaf? ctoken => [extree leaf ctoken];
		~((special? ctoken) and (leftParen? ctoken)) => {
			setError!(parser, PARSER__LPAREN__MISSING);
			failed;
		}
		ctoken := nextToken! parser;
		eof? ctoken => { setError!(parser, PARSER__EOF); failed; }
		operator? ctoken => prefix!(parser, operator ctoken);
		list!(parser, ctoken);
	}
}
