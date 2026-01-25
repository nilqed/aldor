-- ======================================================================
-- Copyright (C) 1991-2010, The Numerical Algorithms Group Ltd.
-- All rights reserved.
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
--
-- * Redistributions of source code must retain the above copyright
--  notice, this list of conditions and the following disclaimer.
--
-- * Redistributions in binary form must reproduce the above copyright
--  notice, this list of conditions and the following disclaimer in
--  the documentation and/or other materials provided with the
--  distribution.
--
-- * Neither the name of The Numerical Algorithms Group Ltd. nor the
--  names of its contributors may be used to endorse or promote products
--  derived from this software without specific prior written permission.
--
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
-- IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
-- TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
-- PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
-- OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
-- EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
-- PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
-- PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
-- LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
-- NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
-- SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
-- ======================================================================
-- 
-------------------------------- rtexns.as ---------------------------------
--
-- This file provides aldorRuntimeException and aldorUnhandledException
-- which are currently required by libfoam, but not provided by it.
-- It is derived from the rtexns.as file belonging to NAG Ltd.
--
-- The way libfoam is compiled, it must have the name rtexns.as
--
-- Copyright (c) The Numerical Algorithms Group Limited 1991-1998
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

export {
	aldorRuntimeException: Pointer -> ();
	aldorUnhandledException: Pointer -> ();
} to Foreign Builtin;

-- should print and raise exception...
-- error is a C-string, which is not the same as a salli debug String
aldorRuntimeException(error:Pointer):() == runtimeError(error)$ExceptionPackage;

aldorUnhandledException(p:Pointer):() == unhandledHandler(p)$ExceptionPackage;

define RuntimeException: Category == with {
	name: () -> String;
	printError: TextWriter -> ();
}

-- s is a C-string, which is not the same as a salli debug String
RuntimeError(s: Pointer): RuntimeException == add {
	name(): String == string s;
	printError(o: TextWriter): () == { import from String; o << name(); }
}

ExceptionPackage: with {
	unhandledHandler: Pointer -> ();
	installHandler: (Pointer -> ()) -> ();
	defaultHandler: Pointer -> ();
	runtimeError: Pointer -> ();
} == add {
	defaultHandler(p: Pointer): () == {
		import from String, TextWriter, WriterManipulator;
		stderr << "Unhandled Exception: " << name p << endnl;
		-- should have a way of adding extra handlers
		printRTInfoIfAny(p pretend with);
	}

	-- horrible hack to get the exception type name,
	-- at least this avoids linking with langx.as from axllib!
	local name(ptr:Pointer):String == {
		macro DN == Record(tag:MachineInteger, p:Pointer);
		macro DV == Record(tag:MachineInteger, namer:Type -> DN);
		macro Dom == Record(dispatcher:DV, domainRep:Type);
		import from DN, DV, Dom;
		dom := ptr pretend Dom;
		dn := (dom.dispatcher.namer) (dom.domainRep);
		dn.tag = 0 => string(dn.p);
		empty;
	}

	printRTInfoIfAny(t: with): () == {
		import from TextWriter, WriterManipulator;
		if t has RuntimeException then {
			printError(stderr)$t;
			stderr << endnl;
		}
	}

	theHandler: Pointer -> () := defaultHandler;

	unhandledHandler(p: Pointer): () == theHandler(p);

	installHandler(f: Pointer -> ()): () == {
		free theHandler := f;
	}
	
	-- s is a C-string, which is not the same as a salli debug String
	runtimeError(s: Pointer): () == throw RuntimeError(s);
}
