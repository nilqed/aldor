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
------------------------------- alg_tokens.as ----------------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1995-1997
--


-- Special token codes
macro {
	TOKEN		== MachineInteger;
	TOK__UNKNOWN	== 100;
	TOK__EOF	== 200;
	TOK__EOEXPR	== 210;
	TOK__LPAREN	== 300;
	TOK__RPAREN	== 301;
	TOK__LBRACKET	== 302;
	TOK__RBRACKET	== 303;
	TOK__LCURLY	== 304;
	TOK__RCURLY	== 305;
	TOK__COMMA	== 310;
}

-- Special parser codes
macro {
	-- parser precedence table 
	PARSER__PLUS	== 0;
	PARSER__MINUS	== 1;
	PARSER__TIMES	== 2;
	PARSER__DIVIDE	== 3;
	PARSER__POWER	== 4;
	PARSER__PREC__SIZE == 5;
	
	-- parser possible precedence level 0 < level 1 < level 2, 
	-- i.e level 2 binds stronger than level 1, and so on.
	PARSER__PREC0	== 0;
	PARSER__PREC1	== 1;
	PARSER__PREC2	== 2;
	
	-- parser error codes
	PARSER__LOOKAHEAD		==  1; -- lookahead was used (int. use)
	PARSER__NOERROR			==  0; -- no error
	PARSER__EOF			== -1; -- end of file
	PARSER__ERROR__IN__EXPR		== -2; -- error in expression
	PARSER__LPAREN__MISSING		== -3; -- ( expected
	PARSER__RPAREN__MISSING		== -4; -- ) expected
	PARSER__RBRACKET__MISSING	== -5; -- ] expected
	PARSER__ASSIGN__MISSING		== -6; -- := expected
}
