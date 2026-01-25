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
------------------------------- leaf.as ----------------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1994
--
-- This type must be included inside "extree.as" to be compiled,
-- but is in a separate file for documentation purposes.

#if ALDOC
\thistype{ExpressionTreeLeaf}
\History{Manuel Bronstein}{24/11/94}{created}
\Usage{import from \this}
\Descr{\this~is a type whose elements are the leafs (atoms) of expression
trees. It provides conversions to and from the basic atomic types.}
\begin{exports}
\category{\astype{OutputType}}\\
\category{\astype{PrimitiveType}}\\
\asexp{aldor}: & (TEXT, \%) $\to$ TEXT & Conversion to \asharp code\\
\asexp{axiom}: & (TEXT, \%) $\to$ TEXT & Conversion to Axiom code\\
\asexp{boolean}: & \% $\to$ \astype{Boolean} & Conversion to a boolean\\
\asexp{boolean?}: & \% $\to$ \astype{Boolean} & Test for a boolean\\
\asexp{C}: & (TEXT, \%) $\to$ TEXT & Conversion to C code\\
\asexp{doubleFloat}:
& \% $\to$ \astype{DoubleFloat} & Conversion to a double precision float\\
\asexp{doubleFloat?}:
& \% $\to$ \astype{Boolean} & Test for a double precision float\\
\asexp{float}: & \% $\to$ \astype{Float} & Conversion to a software big float\\
\asexp{float?}: & \% $\to$ \astype{Boolean} & Test for a software big float\\
\asexp{fortran}: & TEXT, \%) $\to$ TEXT & Conversion to FORTRAN code\\
\asexp{integer}:
& \% $\to$ \astype{Integer} & Conversion to a software big integer\\ 
\asexp{integer?}:
& \% $\to$ \astype{Boolean} & Test for a software big integer\\
\asexp{leaf}: & \astype{Boolean} $\to$ \% & Conversion to a leaf\\
\asexp{leaf}: & \astype{DoubleFloat} $\to$ \% & Conversion to a leaf\\
\asexp{leaf}: & \astype{MachineInteger} $\to$ \% & Conversion to a leaf\\
\asexp{leaf}: & \astype{Integer} $\to$ \% & Conversion to a leaf\\
% \asexp{leaf}: & \astype{Float} $\to$ \% & Conversion to a leaf\\
\asexp{leaf}: & \astype{SingleFloat} $\to$ \% & Conversion to a leaf\\
\asexp{leaf}: & \astype{String} $\to$ \% & Conversion to a leaf\\
\asexp{leaf}: & \astype{Symbol} $\to$ \% & Conversion to a leaf\\
\asexp{lisp}: & (TEXT, \%) $\to$ TEXT & Conversion to Lisp code\\
\asexp{singleFloat}:
& \% $\to$ \astype{SingleFloat} & Conversion to a single precision float\\
\asexp{singleFloat?}:
& \% $\to$ \astype{Boolean} & Test for a single precision float\\
\asexp{machineInteger}:
& \% $\to$ \astype{MachineInteger} & Conversion to a machine integer\\
\asexp{machineInteger?}:
& \% $\to$ \astype{Boolean} & Test for a machine integer\\
\asexp{maple}: & (TEXT, \%) $\to$ TEXT & Conversion to Maple code\\
\asexp{string}: & \% $\to$ \astype{String} & Conversion to a string\\
\asexp{string?}: & \% $\to$ \astype{Boolean} & Test for a string\\
\asexp{symbol}: & \% $\to$ \astype{Symbol} & Conversion to a symbol\\
\asexp{symbol?}: & \% $\to$ \astype{Boolean} & Test for a symbol\\
\asexp{tex}: & (TEXT, \%) $\to$ TEXT & Conversion to \LaTeX\\
\asexp{texParen?}: & \% $\to$ \astype{Boolean} & Check whether to parenthetize\\
\end{exports}
\begin{aswhere}
TEXT &==& \astype{TextWriter}\\
\end{aswhere}
#endif

ExpressionTreeLeaf: Join(OutputType, PrimitiveType) with {
	aldor:		(TEXT, %) -> TEXT;
	axiom:		(TEXT, %) -> TEXT;
	C:		(TEXT, %) -> TEXT;
	fortran:	(TEXT, %) -> TEXT;
	lisp:		(TEXT, %) -> TEXT;
	maple:		(TEXT, %) -> TEXT;
	tex:		(TEXT, %) -> TEXT;
#if ALDOC
\aspage{aldor,axiom,C,fortran,lisp,maple,tex}
\astarget{aldor}
\astarget{axiom}
\astarget{C}
\astarget{fortran}
\astarget{lisp}
\astarget{maple}
\astarget{tex}
\Usage{{\em format}(p, a)}
\Signature{(\astype{TextWriter}, \%)}{\astype{TextWriter}}
\Params{
{\em p} & \astype{TextWriter} & The port to write to\\
{\em a} & \% & A leaf\\
}
\Descr{Writes to $p$ the expression corresponding to the leaf $a$
in the requested format.}
#endif
	boolean:	% -> Boolean;
	boolean?:	% -> Boolean;
#if ALDOC
\aspage{boolean}
\astarget{\name?}
\Usage{ \name~a\\ \name?~a }
\Signatures{
\name: & \% $\to$ \astype{Boolean}\\
\name?: & \% $\to$ \astype{Boolean}\\
}
\Params{ {\em a} & \% & A leaf\\ }
\Retval{
\name~a returns the value of $a$ as a \astype{Boolean}
if that is the type of $a$.\\
\name?~a returns \true~if a is a \astype{Boolean}, \false~otherwise.
}
#endif
	doubleFloat:	% -> DoubleFloat;
	doubleFloat?:	% -> Boolean;
#if ALDOC
\aspage{doubleFloat}
\astarget{\name?}
\Usage{ \name~a\\ \name?~a }
\Signatures{
\name: & \% $\to$ \astype{DoubleFloat}\\
\name?: & \% $\to$ \astype{Boolean}\\
}
\Params{ {\em a} & \% & A leaf\\ }
\Retval{
\name~a returns the value of $a$ as a \astype{DoubleFloat}
if that is the type of $a$.\\
\name?~a returns \true~if a is a \astype{DoubleFloat}, \false~otherwise.
}
#endif
	float:		% -> Float;
	float?:		% -> Boolean;
#if ALDOC
\aspage{float}
\astarget{\name?}
\Usage{ \name~a\\ \name?~a }
\Signatures{
\name: & \% $\to$ \astype{Float}\\
\name?: & \% $\to$ \astype{Boolean}\\
}
\Params{ {\em a} & \% & A leaf\\ }
\Retval{
\name~a returns the value of $a$ as a \astype{Float}
if that is the type of $a$.\\
\name?~a returns \true~if a is a \astype{Float}, \false~otherwise.
}
#endif
	integer:	% -> Integer;
	integer?:	% -> Boolean;
#if ALDOC
\aspage{integer}
\astarget{\name?}
\Usage{ \name~a\\ \name?~a }
\Signatures{
\name: & \% $\to$ \astype{Integer}\\
\name?: & \% $\to$ \astype{Boolean}\\
}
\Params{ {\em a} & \% & A leaf\\ }
\Retval{
\name~a returns the value of $a$ as an \astype{Integer}
if that is the type of $a$.\\
\name?~a returns \true~if a is an \astype{Integer}, \false~otherwise.
}
#endif
	leaf:		Boolean -> %;
	leaf:		DoubleFloat -> %;
	leaf:		Float -> %;
	leaf:		Integer -> %;
	leaf:		MachineInteger -> %;
	leaf:		SingleFloat -> %;
	leaf:		String -> %;
	leaf:		Symbol -> %;
#if ALDOC
\aspage{leaf}
\Usage{\name~a}
\Signatures{
\name: & \astype{Boolean} $\to$ \%\\
\name: & \astype{DoubleFloat} $\to$ \%\\
\name: & \astype{Integer} $\to$ \%\\
\name: & \astype{Float} $\to$ \%\\
\name: & \astype{MachineInteger} $\to$ \%\\
\name: & \astype{SingleFloat} $\to$ \%\\
\name: & \astype{String} $\to$ \%\\
\name: & \astype{Symbol} $\to$ \%\\
}
\Params{
{\em a} & \astype{Boolean} & A constant\\
& \astype{DoubleFloat} &\\
& \astype{Float} &\\
& \astype{Integer} &\\
& \astype{MachineInteger} &\\
& \astype{SingleFloat} &\\
& \astype{String} &\\
& \astype{Symbol} &\\
}
\Retval{\name~a returns $a$ as a leaf.}
\Remarks{A string leaf prints with quotes,
and should be used for string constants, while a symbol leaf prints without
quotes, and should be used for names.}
#endif
	negate:		% -> %;
#if ALDOC
\aspage{negate}
\Usage{\name~a}
\Signature{\%}{\%}
\Params{ {\em a} & \% & A leaf\\ }
\Retval{Returns the leaf $-a$ if $a$ is a numerical leaf, $a$ otherwise.}
\seealso{\asexp{negative?}}
#endif
	negative?:	% -> Boolean;
#if ALDOC
\aspage{negative?}
\Usage{\name~a}
\Signature{\%}{\astype{Boolean}}
\Params{ {\em a} & \% & A leaf\\ }
\Retval{Returns \true~if $a$ is a numerical leaf and $a < 0$, \false~otherwise.}
\seealso{\asexp{negate}}
#endif
	machineInteger:	% -> MachineInteger;
	machineInteger?:	% -> Boolean;
#if ALDOC
\aspage{machineInteger}
\astarget{\name?}
\Usage{ \name~a\\ \name?~a }
\Signatures{
\name: & \% $\to$ \astype{MachineInteger}\\
\name?: & \% $\to$ \astype{Boolean}\\
}
\Params{ {\em a} & \% & A leaf\\ }
\Retval{
\name~a returns the value of $a$ as a \astype{MachineInteger}
if that is the type of $a$.\\
\name?~a returns \true~if a is a \astype{MachineInteger}, \false~otherwise.
}
#endif
	singleFloat:	% -> SingleFloat;
	singleFloat?:	% -> Boolean;
#if ALDOC
\aspage{singleFloat}
\astarget{\name?}
\Usage{ \name~a\\ \name?~a }
\Signatures{
\name: & \% $\to$ \astype{SingleFloat}\\
\name?: & \% $\to$ \astype{Boolean}\\
}
\Params{ {\em a} & \% & A leaf\\ }
\Retval{
\name~a returns the value of $a$ as a \astype{SingleFloat}
if that is the type of $a$.\\
\name?~a returns \true~if a is a \astype{SingleFloat}, \false~otherwise.
}
#endif
	string:		% -> String;
	string?:	% -> Boolean;
#if ALDOC
\aspage{string}
\astarget{\name?}
\Usage{ \name~a\\ \name?~a }
\Signatures{
\name: & \% $\to$ \astype{String}\\
\name?: & \% $\to$ \astype{Boolean}\\
}
\Params{ {\em a} & \% & A leaf\\ }
\Retval{
\name~a returns the value of $a$ as a \astype{String}
if that is the type of $a$.\\
\name?~a returns \true~if a is a \astype{String}, \false~otherwise.
}
#endif
	symbol:		% -> Symbol;
	symbol?:	% -> Boolean;
#if ALDOC
\aspage{symbol}
\astarget{\name?}
\Usage{ \name~a\\ \name?~a }
\Signatures{
\name: & \% $\to$ \astype{Symbol}\\
\name?: & \% $\to$ \astype{Boolean}\\
}
\Params{ {\em a} & \% & A leaf\\ }
\Retval{
\name~a returns the value of $a$ as a \astype{Symbol}
if that is the type of $a$.\\
\name?~a returns \true~if a is a \astype{Symbol}, \false~otherwise.
}
#endif
	texParen?:	% -> Boolean;
#if ALDOC
\aspage{texParen?}
\Usage{\name~a}
\Signature{\%}{\astype{Boolean}}
\Params{ {\em a} & \% & A leaf\\ }
\Retval{Returns \true~if the leaf $a$ should be parenthetized,
\false~otherwise.}
#endif
} == add {
	macro {
		Rep == Union(ubool: Boolean, usint: MachineInteger,
				usfl: SingleFloat, udblf: DoubleFloat,
				ufloat: Float,
				uint: Integer, ustr: String, usym: Symbol);
	}

	import from Rep;

	sample:%			== leaf(1@MachineInteger);
	leaf(n:MachineInteger):%	== per [n];
	leaf(x:SingleFloat):%		== per [x];
	leaf(x:DoubleFloat):%		== per [x];
	leaf(n:Integer):%		== per [n];
	leaf(x:Float):%			== per [x];
	leaf(b:Boolean):%		== per [b];
	leaf(s:String):%		== per [s];
	leaf(s:Symbol):%		== per [s];
	machineInteger?(l:%):Boolean	== rep(l) case usint;
	integer?(l:%):Boolean		== rep(l) case uint;
	doubleFloat?(l:%):Boolean	== rep(l) case udblf;
	singleFloat?(l:%):Boolean	== rep(l) case usfl;
	float?(l:%):Boolean		== rep(l) case ufloat;
	boolean?(l:%):Boolean		== rep(l) case ubool;
	boolean(l:%):Boolean		== { assert(boolean? l); rep(l).ubool;}
	integer(l:%):Integer		== { assert(integer? l); rep(l).uint; }
	float(l:%):Float		== { assert(float? l); rep(l).ufloat; }
	(p:TEXT) << (l:%):TEXT		== str(p, l, "_"", "_"");
	tex(p:TEXT, l:%):TEXT		== str(p, l, "``", "''");
	maple(p:TEXT, l:%):TEXT		== str(p, l, "`", "`");
	axiom(p:TEXT, l:%):TEXT		== p << l;
	aldor(p:TEXT, l:%):TEXT		== p << l;
	fortran(p:TEXT, l:%):TEXT	== C(p, l);
	texParen?(l:%):Boolean		== false;
	string(l:%):String		== { assert(string? l); rep(l).ustr; }
	string?(l:%):Boolean		== rep(l) case ustr;
	symbol(l:%):Symbol		== { assert(symbol? l); rep(l).usym; }
	symbol?(l:%):Boolean		== rep(l) case usym;

	doubleFloat(l:%):DoubleFloat == {
		assert(doubleFloat? l);
		rep(l).udblf;
	}

	singleFloat(l:%):SingleFloat == {
		assert(singleFloat? l);
		rep(l).usfl;
	}

	machineInteger(l:%):MachineInteger == {
		assert(machineInteger? l);
		rep(l).usint;
	}

	C(p:TEXT, l:%):TEXT == {
		boolean? l => {
			boolean l => p << "1";
			p << "0";
		}
		p << l;
	}

	lisp(p:TEXT, l:%):TEXT == {
		boolean? l => {
			boolean l => p << "t";
			p << "nil";
		}
		p << l;
	}

	(a:%) = (b:%):Boolean == {
		integer? a => integer? b and integer a = integer b;
		machineInteger? a =>
			machineInteger? b and machineInteger a=machineInteger b;
		float? a => float? b and float a = float b;
		doubleFloat? a =>
			doubleFloat? b and doubleFloat a = doubleFloat b;
		singleFloat? a =>
			singleFloat? b and singleFloat a = singleFloat b;
		string? a => string? b and string a = string b;
		symbol? a => symbol? b and symbol a = symbol b;
		boolean? a and boolean? b and boolean a = boolean b;
	}

	local str(p:TEXT, l:%, opq:String, clq:String):TEXT == {
		machineInteger? l => p << machineInteger l;
		singleFloat? l => p << singleFloat l;
		doubleFloat? l => p << doubleFloat l;
		integer? l => p << integer l;
		float? l => p << float l;
		boolean? l => p << boolean l;
		symbol? l => p << symbol l;
		p << opq << string l << clq;
	}

	negative?(l:%):Boolean == {
		machineInteger? l => machineInteger l < 0;
		doubleFloat? l => doubleFloat l < 0;
		singleFloat? l => singleFloat l < 0;
		integer? l => integer l < 0;
		float? l => float l < 0;
		false;
	}

	negate(l:%):% == {
		machineInteger? l => leaf(- machineInteger l);
		doubleFloat? l => leaf(- doubleFloat l);
		singleFloat? l => leaf(- singleFloat l);
		integer? l => leaf(- integer l);
		float? l => leaf(- float l);
		l;
	}
}
