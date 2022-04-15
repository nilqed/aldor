--------------------------- sit_prfcat0.as --------------------------------
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "algebra"


define PrimeFieldCategory0:Category == Join(FiniteField,SerializableType) with {
    lift: % -> Integer;

		default {
			degree:Integer		== 1;
			pthPower(a:%):%		== a;
			pthPower!(a:%):%	== a;
			pthRoot(a:%):%		== a;
			pthRoot!(a:%):%		== a;
			index(a:%):Integer	== lift a;

			(port:BinaryWriter) << (a:%):BinaryWriter == {
				import from Integer;
				port << lift a;
			}

			<< (port:BinaryReader):% == {
				import from Integer;
				(<< port)@Integer :: %;
			}

			lookup(n:Integer):% == {
				assert(n >= 0); -- assert(n < #$%); BUG 1181
				n::%;
			}

			-- TEMPORARY: BUG 1181
			-- #:Integer		== characteristic$%;

			extree(x:%):ExpressionTree == { 
				import from Integer;
				extree lift x;
			}
		}
}
