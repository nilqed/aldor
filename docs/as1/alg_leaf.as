------------------------------- alg_leaf.as ----------------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1994
--
-- This type must be included inside "sit_extree.as" to be compiled,
-- but is in a separate file for documentation purposes.


ExpressionTreeLeaf: Join(OutputType, PrimitiveType) with {
	aldor:		(TEXT, %) -> TEXT;
	axiom:		(TEXT, %) -> TEXT;
	C:		(TEXT, %) -> TEXT;
	fortran:	(TEXT, %) -> TEXT;
	infix:		(TEXT, %) -> TEXT;
	lisp:		(TEXT, %) -> TEXT;
	maple:		(TEXT, %) -> TEXT;
	tex:		(TEXT, %) -> TEXT;
	boolean:	% -> Boolean;
	boolean?:	% -> Boolean;
	doubleFloat:	% -> DoubleFloat;
	doubleFloat?:	% -> Boolean;
#if GMP
	float:		% -> Float;
#endif
	float?:		% -> Boolean;
	integer:	% -> Integer;
	integer?:	% -> Boolean;
	leaf:		Boolean -> %;
	leaf:		DoubleFloat -> %;
#if GMP
	leaf:		Float -> %;
#endif
	leaf:		Integer -> %;
	leaf:		MachineInteger -> %;
	leaf:		SingleFloat -> %;
	leaf:		String -> %;
	leaf:		Symbol -> %;
	negate:		% -> %;
	negative?:	% -> Boolean;
	machineInteger:	% -> MachineInteger;
	machineInteger?:	% -> Boolean;
	singleFloat:	% -> SingleFloat;
	singleFloat?:	% -> Boolean;
	string:		% -> String;
	string?:	% -> Boolean;
	symbol:		% -> Symbol;
	symbol?:	% -> Boolean;
	texParen?:	% -> Boolean;
} == add {
	macro {
		Rep == Union(ubool: Boolean, usint: MachineInteger,
				usfl: SingleFloat, udblf: DoubleFloat,
#if GMP
				ufloat: Float,
#endif
				uint: Integer, ustr: String, usym: Symbol);
	}

	import from Rep;

	sample:%			== leaf(1@MachineInteger);
	leaf(n:MachineInteger):%	== per [n];
	leaf(x:SingleFloat):%		== per [x];
	leaf(x:DoubleFloat):%		== per [x];
	leaf(n:Integer):%		== per [n];
	leaf(b:Boolean):%		== per [b];
	leaf(s:String):%		== per [s];
	leaf(s:Symbol):%		== per [s];
	machineInteger?(l:%):Boolean	== rep(l) case usint;
	integer?(l:%):Boolean		== rep(l) case uint;
	doubleFloat?(l:%):Boolean	== rep(l) case udblf;
	singleFloat?(l:%):Boolean	== rep(l) case usfl;
	boolean?(l:%):Boolean		== rep(l) case ubool;
	boolean(l:%):Boolean		== { assert(boolean? l); rep(l).ubool;}
	integer(l:%):Integer		== { assert(integer? l); rep(l).uint; }
	(p:TEXT) << (l:%):TEXT		== str(p, l, "_"", "_"");
	tex(p:TEXT, l:%):TEXT		== str(p, l, "``", "''");
	maple(p:TEXT, l:%):TEXT		== str(p, l, "`", "`");
	axiom(p:TEXT, l:%):TEXT		== p << l;
	aldor(p:TEXT, l:%):TEXT		== p << l;
	infix(p:TEXT, l:%):TEXT		== p << l;
	fortran(p:TEXT, l:%):TEXT	== C(p, l);
	texParen?(l:%):Boolean		== false;
	string(l:%):String		== { assert(string? l); rep(l).ustr; }
	string?(l:%):Boolean		== rep(l) case ustr;
	symbol(l:%):Symbol		== { assert(symbol? l); rep(l).usym; }
	symbol?(l:%):Boolean		== rep(l) case usym;
#if GMP
	leaf(x:Float):%			== per [x];
	float(l:%):Float		== { assert(float? l); rep(l).ufloat; }
	float?(l:%):Boolean		== rep(l) case ufloat;
#else
	local float(l:%):MachineInteger	== never;
	float?(l:%):Boolean		== false;
#endif

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
