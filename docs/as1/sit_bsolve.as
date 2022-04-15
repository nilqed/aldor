------------------------------ sit_bsolve.as --------------------------------
-- Copyright (c) Thom Mulders 1996
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1996
-----------------------------------------------------------------------------

#include "algebra"

macro {
	Z == MachineInteger;
	ARR == PrimitiveArray;
	Sn == Permutation n;
	V == Vector;
}


Backsolve(R:IntegralDomain,M:MatrixCategory R): with {
	backsolve: (M,Z->Z,ARR Z,Z,Z,R) -> V R;
	backsolve: (M,Z->Z,ARR Z,Z,M,R) -> (M, V R);
	if R has GcdDomain then {
		backsolve: (M,Z->Z,ARR Z,Z,Z) -> V R;
		backsolve: (M,Z->Z,ARR Z,Z,M) -> (M,V R);
		backsolve2: (M,Z->Z,ARR Z,Z,Z,R) -> V R;
		backsolve2: (M,Z->Z,ARR Z,Z,M,R) -> (M,V R);
	}
} == add {
	backsolve(a:M,p:Z->Z,st:ARR Z,r:Z,c:Z,d:R): V R == {
		m := numberOfColumns a;
		v := zero m;
		v(c) := d;
		for i in r..1 by -1 repeat {
			e := -d * a(p(i),c);
			for j in next(i)..r repeat
				e := e - a(p(i),st(j)) * v(st(j));
			v(st(i)) := quotient(e,a(p(i),st(i)));
		}
		v;
	}

	backsolve(a:M,p:Z->Z,st:ARR Z,r:Z,b:M,d:R): (M,V R) == {
		(n, m) := dimensions a;
		s := numberOfColumns b;
		sol := zero(m,s);
		den:V R := new(s, d);
		for k in 1..s repeat {
			for j in next(r)..n repeat {
				if b(p(j),k)~=0 then { den(k) := 0; break }
			}
			if den(k)~=0 then for i in r..1 by -1 repeat {
				e := d * b(p(i), k);
				for j in next(i)..r repeat
					e := e-a(p(i),st(j))*sol(st(j),k);
				sol(st(i),k) := quotient(e,a(p(i),st(i)));
			}
		}
		(sol,den);
	}

	if R has GcdDomain then {
		local field?:Boolean == R has Field;

		backsolve(a:M,p:Z->Z,st:ARR Z,r:Z,c:Z): V R == {
			import from R,Partial R;
			field? => backsolve(a,p,st,r,c,1);
			m := numberOfColumns a;
			v := zero m;
			v(c) := 1;
			for i in r..1 by -1 repeat {
				e := -v(c)*a(p(i),c);
				for j in next(i)..r repeat
					e := e-a(p(i),st(j))*v(st(j));
				q := exactQuotient(e,a(p(i),st(i)));
				if failed? q then {
					(g,f1,f2) := gcdquo(e,a(p(i),st(i)));
					v(c) := f2*v(c);
					for j in next(i)..r repeat
						v(st(j)) := f2*v(st(j));
					v(st(i)) := f1;
				}
				else v(st(i)) := retract q;
			}
			v;
		}

		backsolve(a:M,p:Z->Z,st:ARR Z,r:Z,b:M): (M,V R) == {
			import from R,Partial R;
			field? => backsolve(a,p,st,r,b,1);
			(n, m) := dimensions a;
			s := numberOfColumns b;
			sol := zero(m,s);
			den:V R := new(s, 1);
			for k in 1..s repeat {
				for j in next(r)..n repeat
					if b(p(j),k)~=0 then {
						den(k) := 0;
						break;
					}
				if den(k)=0 then iterate;
				for i in r..1 by -1 repeat {
					e := den(k)*b(p(i),k);
					for j in i+1..r repeat
						e:=e-a(p(i),st(j))*sol(st(j),k);
					q := exactQuotient(e,a(p(i),st(i)));
					if failed? q then {
						(g,f1,f2) :=
							gcdquo(e,a(p(i),st(i)));
						den(k) := f2*den(k);
						for j in next(i)..r repeat
							sol(st(j),k) :=
								f2*sol(st(j),k);
						sol(st(i),k) := f1;
					}
					else sol(st(i),k) := retract q;
				}
			}
			(sol,den);
		}

		backsolve2(a:M,p:Z->Z,st:ARR Z,r:Z,c:Z,d:R): V R == {
			import from List R;
			field? => backsolve(a,p,st,r,c,1);
			m := numberOfColumns a;
			v := zero m;
			v(c) := d;
			for i in r..1 by -1 repeat {
				e := -d*a(p(i),c);
				for j in next(i)..r repeat
					e := e-a(p(i),st(j))*v(st(j));
				v(st(i)) := quotient(e,a(p(i),st(i)));
			}
			l:List R := [v(st(i)) for i in 1..r];
			l := cons(v(c),l);
			g := gcd generator l;
			v(c) := quotient(v(c),g);
			for i in 1..r repeat
				v(st(i)) := quotient(v(st(i)),g);
			v;
		}

		backsolve2(a:M,p:Z->Z,st:ARR Z,r:Z,b:M,d:R): (M,V R) == {
			import from List R;
			field? => backsolve(a,p,st,r,b,1);
			(n, m) := dimensions a;
			s := numberOfColumns b;
			sol := zero(m,s);
			den:V R := new(s, d);
			for k in 1..s repeat {
				for j in next(r)..n repeat
					if b(p(j),k)~=0 then {
						den(k) := 0;
						break;
					}
				if den(k)=0 then
					iterate;
				for i in r..1 by -1 repeat {
					e := d*b(p(i),k);
					for j in next(i)..r repeat
						e:=e-a(p(i),st(j))*sol(st(j),k);
					sol(st(i),k):=quotient(e,a(p(i),st(i)));
				}
				l:List R := [sol(st(i),k) for i in 1..r];
				l := cons(den(k),l);
				g := gcd generator l;
				den(k) := quotient(den(k),g);
				for i in 1..r repeat
					sol(st(i),k):= quotient(sol(st(i),k),g);
			}
			(sol,den);
		}

	}
}
