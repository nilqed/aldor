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
---------------------------- shasta.as -----------------------------
--
-- Copyright (c) Manuel Bronstein 2000-2001
-- Copyright (c) INRIA 2000-2001, Version 0.1.13
-- Logiciel Shasta (c) INRIA 2000-2001, dans sa version 0.1.13
-----------------------------------------------------------------------------

#include "sumit"
#include "aldorio"

macro Z == Integer;

#library lib1 "multlodo.ao"
#library lib2 "evalodo.ao"
import from lib1, lib2;
inline from lib1, lib2;

local shasta(P:Parser, p:P, format:String, x:Symbol, dx:Symbol,
		v?:Boolean, t?:Boolean, done:String):()=={
	macro {
		ZX	== DenseUnivariatePolynomial(Z, x);
		Q	== Fraction Z;
		QX	== DenseUnivariatePolynomial(Q, x);
		Qx	== Fraction QX;
		Qxd	== LinearOrdinaryRecurrenceQ(Q, QX, dx);
		R	== MultiLodo(ZX, QX, Qxd);
	}
	import from Z, Q, QX, Qx, Qxd, R, SymbolTable R;
	import from Shell(P, R, LODOEvaluator(ZX, QX, Qxd));
	import from SumitLibraryInformation, List String;
	if v? then {
		banner(stderr, "S H A S T A 1.0.2");
		for line in credits repeat stderr << line << newline;
		stderr << newline;
		stderr << "Input format = " << format << newline;
		stderr << "Independent variable = " << x << newline;
		stderr << "Shift = " << dx << newline;
	}
	t := table();
	t.x := monom$QX :: R;
	t.dx := monom$Qxd :: R;
	shell!(p, stdout, stderr, t, v?, t?, done);
}

local shasta(P:ParserReader, format:String, x:Symbol, dx:Symbol,
	v?:Boolean, t?:Boolean, done:String):() ==
		shasta(P, parser(stdin)$P, format, x, dx, v?, t?, done);

local parser(format:String):ParserReader == {
	format = "infix" => InfixExpressionParser;
	format = "lisp" => LispExpressionParser;
	error "shasta: unknown input format -- use -i lisp or -i infix";
}

main():() == {
	import from Boolean, Symbol, CommandLine, List String;
	prefix := "einw";
	lder := flag(char "e", prefix);
	der := { empty? lder => "E"; first lder; }
	lvar := flag(char "n", prefix);
	x := { empty? lvar => "n"; first lvar; }
	lformat := flag(char "i", prefix);
	format := { empty? lformat => "infix"; first lformat; }
	ldone := flag(char "w", prefix);
	done := { empty? ldone => empty; first ldone; }
	shasta(parser format, format, -x, -der,
		~flag?(char "q", prefix), flag?(char "t", prefix), done);
}

main();
