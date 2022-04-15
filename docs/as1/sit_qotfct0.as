------------------------ sit_qotfct0.as ---------------------------
-- Copyright (c) Laurent Bernardin 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995
-----------------------------------------------------------------------------

#include "algebra"


define FractionFieldCategory0(R: IntegralDomain): Category ==
	Join(Field, FractionCategory R) with {
	if R has CharacteristicZero then RittRing;
	if R has SerializableType then SerializableType;
	if R has TotallyOrderedType then TotallyOrderedType;
	if R has Parsable then Parsable;
	/:		(R, R) -> %;
	default {
		import from R;

		(p:R) * (a:%):% == (p * numerator a) / (denominator a);
		random():%	== random()$R / random()$R;

		relativeSize(a:%):MachineInteger ==
			relativeSize(numerator a) + relativeSize(denominator a);

		if R has CharacteristicZero then inv(n:Integer):% == 1 / (n::R);

		(a:%) + (b:%):% == {
			(numerator a * denominator b +
				denominator a * numerator b) /
					(denominator a * denominator b);
		}
	
		(a:%) * (b:%):% == {
			(numerator a * numerator b) /
				(denominator a * denominator b);
		}

		(a:%) = (b:%):Boolean == {
			numerator a * denominator b =
				denominator a * numerator b;
		}

		if R has TotallyOrderedType then {
			(a:%) < (b:%):Boolean == {
				numerator(a) * denominator(b) <
					numerator(b) * denominator(a);
			}
		}

		lift(D:Derivation R):Derivation % == {
			import from Integer;
			derivation {(f:%):% +-> {
				n := numerator f; d := denominator f;
				D(n) / d - n * (D(d) / d^2);
			} }
		}

		if R has FiniteCharacteristic then {
			pthPower(a:%):% ==
				pthPower(numerator a) / pthPower(denominator a);
		}

		if R has SerializableType then {
			(port:BinaryWriter) << (a:%):BinaryWriter == {
				import from R;
				port << numerator a << denominator a;
			}

			<< (port:BinaryReader):% == {
				n:R := << port;
				n / (<< port)@R;
			}
		}

		if R has Parsable then {
			eval(t:ExpressionTreeLeaf):Partial % == {
				import from Partial R;
				failed?(u := eval(t)$R) => failed;
				[retract(u)::%];
			}

			eval(op:MachineInteger,
				args:List ExpressionTree):Partial % == {
					import from ParsingTools %;
					evalArith(op, args);
			}
		}
	}
}		
