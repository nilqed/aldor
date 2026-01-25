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
------------------------------- sit_basic.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "sumit"
#include "uid"

macro {
	Z == MachineInteger;
	TREE == ExpressionTree;
	LEAF == ExpressionTreeLeaf;
}

#if ALDOC
\thistype{SumitType}
\History{Manuel Bronstein}{21/11/94}{created}
\Usage{\this: Category}
\Descr{\this~is the category of basic \sumit types.}
\begin{exports}
\category{\astype{OutputType}}\\
\category{\astype{PrimitiveType}}\\
\asexp{extree}:
& \% $\to$ \astype{ExpressionTree} & Conversion to an expression tree\\
\asexp{relativeSize}:
& \% $\to$ \astype{MachineInteger} & Complexity measure\\
\end{exports}
#endif

define SumitType: Category == Join(OutputType, PrimitiveType) with {
	extree: % -> TREE;
#if ALDOC
\aspage{extree}
\Usage{\name~x}
\Signature{\%}{\astype{ExpressionTree}}
\Params{ {\em x} & \% & The element to convert\\ }
\Descr{Converts $x$ to an expression tree.}
#endif
	relativeSize: % -> MachineInteger;
#if ALDOC
\aspage{relativeSize}
\Usage{\name~x}
\Signature{\%}{\astype{MachineInteger}}
\Params{ {\em x} & \% & An element of the type\\ }
\Retval{Returns some measure of the complexity of x.}
\Remarks{This measure does not have to be absolute, but it should
be usable to compare 2 elements of the type
and decide which one is the ``cheapest'' for calculations.
This measure has no mathematical meaning in general, but can
be used for selection strategies, for example in Gaussian
elimination.}
#endif
	default {
		relativeSize(x:%):MachineInteger == 1;

		(port:TextWriter) << (a:%):TextWriter == {
			import from TREE;
			tex(port, extree a);
		}
	}
}

extend Boolean: Join(Parsable, SumitType) == add {
	extree(x:%):TREE == {
		import from LEAF;
		extree leaf(x pretend Boolean);
		-- extree leaf x;
	}

	eval(t:LEAF):Partial % == {
		boolean? t => [boolean t];
		failed;
	}

	eval(op:Z, args:List TREE):Partial % == {
		local u:Partial %;
		op = UID__AND => {
			empty? args or failed?(u := eval first args) => failed;
			ans? := retract u;
			for arg in rest args while ans? repeat {
				failed?(u := eval arg) => return failed;
				ans? := retract u;
			}
			[ans?];
		}
		op = UID__OR => {
			empty? args or failed?(u := eval first args) => failed;
			ans? := retract u;
			for arg in rest args while(~ans?) repeat {
				failed?(u := eval arg) => return failed;
				ans? := retract u;
			}
			[ans?];
		}
		op = UID__NOT => {
			empty? args or ~empty?(rest args)
				or failed?(u := eval first args) => failed;
			[~retract u];
		}
		failed;
	}
}

extend String: Join(Parsable, SumitType) == add {
	relativeSize(x:%):MachineInteger == #x;

	extree(x:%):TREE == {
		import from LEAF;
		extree leaf(x pretend String);
		-- extree leaf x;
	}

	eval(t:LEAF):Partial % == {
		import from Symbol;
		string? t => [string t];
		symbol? t => [name symbol t];
		failed;
	}

	eval(op:Z, args:List TREE):Partial % == {
		op = UID__PLUS => {
			ans:% := empty;
			for arg in args repeat {
				u := eval(arg)@Partial(%);
				failed? u => return failed;
				ans := ans + retract u;
			}
			[ans];
		}
		failed;
	}
}

extend Symbol: Join(Parsable, SumitType) == add {
	extree(x:%):TREE == {
		import from LEAF;
		extree leaf(x pretend Symbol);
		-- extree leaf x;
	}

	eval(t:LEAF):Partial % == {
		string? t => [- string t];
		symbol? t => [symbol t];
		failed;
	}

	eval(op:Z, args:List TREE):Partial % == {
		import from Boolean, String, Partial String;
		op = UID__PLUS => {
			ans:String := empty;
			for arg in args repeat {
				u := eval(arg)@Partial(String);
				failed? u => return failed;
				ans := ans + retract u;
			}
			[-ans];
		}
		op = UID__MINUS => {
			empty? args or ~empty?(rest args)
				or failed?(u:=eval first(args)@Partial(String))
					=> failed;
			[- retract u];
		}
		failed;
	}
}

extend MachineInteger: Join(Parsable, SumitType) == add {
	relativeSize(x:%):MachineInteger== abs x;

	extree(x:%):TREE == {
		import from LEAF;
		extree leaf(x pretend MachineInteger);
		-- extree leaf x;
	}

	eval(t:LEAF):Partial % == {
		import from Integer;
		machineInteger? t => [machineInteger t];
		integer? t => [machine integer t];
		failed;
	}

	eval(op:Z, args:List TREE):Partial % == {
		import from ParsingTools %;
		evalArith(op, args);
	}
}

extend SingleFloat:Join(Parsable, SumitType) == add {
	extree(x:%):TREE == {
		import from LEAF;
		extree leaf(x pretend SingleFloat);
		-- extree leaf x;
	}

	eval(t:LEAF):Partial % == {
		singleFloat? t => [singleFloat t];
		failed;
	}

	eval(op:Z, args:List TREE):Partial % == {
		import from ParsingTools %;
		evalArith(op, args);
	}
}

extend DoubleFloat:Join(Parsable, SumitType) == add {
	extree(x:%):TREE == {
		import from LEAF;
		extree leaf(x pretend DoubleFloat);
		-- extree leaf x;
	}

	eval(t:LEAF):Partial % == {
		doubleFloat? t => [doubleFloat t];
		failed;
	}
	
	eval(op:Z, args:List TREE):Partial % == {
		import from ParsingTools %;
		evalArith(op, args);
	}
}

extend GMPFloat:Join(Parsable, SumitType) == add {
	extree(x:%):TREE == {
		import from LEAF;
		extree leaf(x pretend GMPFloat);
		-- extree leaf x;
	}

	eval(t:LEAF):Partial % == {
		float? t => [float t];
		failed;
	}
	
	eval(op:Z, args:List TREE):Partial % == {
		import from ParsingTools %;
		evalArith(op, args);
	}
}

