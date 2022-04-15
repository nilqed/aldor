----------------------------- sit_uffalg.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it (c) INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "algebra"

macro {
	Z == Integer;
}


define UnivariateFreeRing(R:Join(ArithmeticType, ExpressionType)): Category ==
	Join(CopyableType, IndexedFreeRRing(R, Z),
		UnivariateFreeLinearArithmeticType R) with {
	coerce: Vector R -> %;
	vectorize!: Vector R -> % -> Vector R;
	companion: % -> DenseMatrix R;
	monomial!: (%, R, Z) -> %;
	random: (Z, () -> R, m:Z == -1) -> %;
	if R has Ring then {
		random: (Z, m:Z == -1) -> %;
	}
	revert: % -> %;
	revert!: % -> %;
--	times: (%, %, Z, Z) -> %;
	default {
		ground?(p:%):Boolean	== { import from Z; zero? degree p; }
		monomial!(p:%,c:R,n:Z):%== term(c, n);
		revert!(p:%):%		== revert p;

		support(p:%):Generator Cross(R, %) == generate {
			import from R, Z;
			for trm in p repeat {
				(c, n) := trm;
				yield (c, monomial n);
			}
		}

		coefficients(p:%):Generator R == generate {
			import from Z;
			for i in 0..degree p repeat yield coefficient(p, i);
		}

		relativeSize(p:%):MachineInteger == {
			import from Z;
			zero? p => 0;
			machine degree p;
		}

		leadingCoefficient(p:%):R == {
			(c, n) := leadingTerm p;
			c;
		}

		degree(p:%):Z == {
			(c, n) := leadingTerm p;
			n;
		}

		trailingCoefficient(p:%):R == {
			(c, n) := trailingTerm p;
			c;
		}

		trailingDegree(p:%):Z == {
			(c, n) := trailingTerm p;
			n;
		}

		shift(p:%, n:Z):% == {
			zero? n => p;
			q:% := 0;
			pos? := n > 0;
			for term in p repeat {
				(a, d) := term;
				e := d + n;
				if pos? or e >= 0 then q := add!(q, a, e);
			}
			q;
		}

		companion(p:%):DenseMatrix R == {
			import from MachineInteger, Z, R;
			zero? p or zero?(d := degree p) => zero(0, 0);
			n := machine d;
			v:Vector R := zero(n := machine d);
			for term in p repeat {
				(c, e) := term;
				ee := machine e;
				if ee < n then v(next ee) := -c;
			}
			companion(v, leadingCoefficient p);
		}

		copy(p:%):% == {
			q:% := 0;
			for term in p repeat {
				(c, n) := term;
				q := add!(q, c, n);
			}
			q;
		}

		map(f:R -> R)(p:%):% == {
			q:% := 0;
			for term in p repeat {
				(c, n) := term;
				q := add!(q, f c, n);
			}
			q;
		}

--		times(a:%, b:%, l:Z, h:Z):% == {
--			p := a * b;
--			s:% := 0;
--			for i in l..min(degree p, h) repeat
--				s := add!(s, coefficient(p, i), i - l);
--			s
--		}

		random(n:Z, f:() -> R, m:Z):% == {
			import from R;
			assert(n >= 0);
			if m < 0 or m > n+1 then m := n+1;
			p := monomial(n) + term(f(), 0);
			for i in 3..m repeat
				p := add!(p, f(), random()@Z rem n);
			p;
		}

		if R has Ring then {
			coerce(n:Z):% == { import from R; term(n::R, 0); }
			random(n:Z, m:Z):% == random(n, random$R, m);

			-- TEMPORARY: 1.1.12p4 DOES NOT SEE THE Algebra DEFAULT
			characteristic:Z == characteristic$R;

			random():% == {
				import from Z;
				d := random()$Z rem 101;
				random(d, (3 * d) quo 4);
			}
		}

		revert(p:%):% == {
			zero? p => p;
			d := degree p;
			q:% := 0;
			-- terms is important so that the high degree terms
			-- are created first (space-efficiency)
			for term in terms p repeat {
				(c, e) := term;		-- low to high
				q := add!(q, c, d - e);
			}
			q;
		}

		vectorize!(v:Vector R): % -> Vector R == {
			import from MachineInteger, Z;
			n := #v;
			(p:%):Vector R +-> {
				for i in 1..n repeat
					v.i := coefficient(p, prev(i)::Z);
				v;
			}
		}

		coerce(v:Vector R):% == {
			import from MachineInteger, Z;
			zero?(n := #v) => 0;
			n1 := prev n;
			p := term(v.n, n1::Z);
			for i in n1..1 by -1 repeat p := add!(p,v.i,prev(i)::Z);
			p;
		}

		-- default is sparse dumping, terminated by 0 P_{-1}
		if R has SerializableType then {
			(port:BinaryWriter) << (p:%):BinaryWriter == {
				import from R, Z;
				for term in p repeat {
					(c, n) := term;
					port := port << c << n;
				}
				port << 0@R << (-1)@Z;
			}

			<< (port:BinaryReader):% == {
				import from R, Z;
				p:% := 0;
				n:Z := 0;
				local c:R;
				while n >= 0 repeat {
					c := << port;
					n := << port;
					if n >= 0 then p := add!(p, c, n);
				}
				p;
			}
		}

		if R has HashType then {
			hash(p:%):MachineInteger == {
				import from R;
				h:MachineInteger := 0;
				for term in p repeat {
					(c, n) := term;
					h := h + hash(c) + machine n;
				}
				h;
			}
		}
	}
}


UnivariateFreeRing2(R:Join(ArithmeticType, ExpressionType),
				RX:UnivariateFreeRing R,
				S:Join(ArithmeticType, ExpressionType),
				SX:UnivariateFreeRing S): with {
	map: (R -> S) -> RX -> SX;
} == add {
	map(f:R -> S)(p:RX):SX == {
		q:SX := 0;
		for term in p repeat {
			(c, n) := term;
			q := add!(q, f c, n);
		}
		q;
	}
}

