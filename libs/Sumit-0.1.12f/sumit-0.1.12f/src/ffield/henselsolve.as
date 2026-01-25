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
---------------------------  henselsolve.as  ------------------------
#include "sumit"

macro SI == SingleInteger;
macro I == Integer;

HenselSolve(Z:IntegerCategory, M:MatrixCategory0 Z,
	F:PrimeFieldCategory0, MF:MatrixCategory0 F): with {

	henselLift: (M, MF, Vector Z, Z) -> (Vector Z, Z);
	henselSolve: (M, MF, Vector Z, Z, Z) -> (Vector Z, Z);
	henselSolve: (M, MF, Vector Z) -> (Vector Z, Z);

} == add {

	macro Q == Partial Cross(Z,Z);

	local p == characteristic$F;

	upgrade(a:MF):M == {
		import from Z,F;

		p2 := p quo 2;

		n:SI := rows a;
		b:M := zero(n, n);
		for i in 1..n repeat
			for j in 1..n repeat {
				b(i,j) := (lift a(i,j))::Z;
				if (integer b(i,j)) > p2 then
					b(i,j) := b(i,j)-p::Z;
			}
		b;
	}

	upgrade(v:Vector F):Vector Z == {
		import from Z,F;

		p2 := p quo 2;

		n:SI := #v;
		b:Vector Z := zero n;
		for i in 1..n repeat {
			b(i) := (lift v(i))::Z;
			if (integer b(i)) > p2 then
				b(i) := b(i)-p::Z;
		}
		b;
	}
	
	downgrade(a:M):MF == {
		import from Z,F,I;

		n:SI := rows a;
		b:MF := zero(n,n);
		for i in 1..n repeat
			for j in 1..n repeat
				b(i,j) := integer(a(i,j))::F;
		b;
	}

	downgrade(v:Vector Z):Vector F == {
		import from Z,F,I;

		n:SI := #v;
		b:Vector F := zero n;
		for i in 1..n repeat
			b(i) := integer(v(i))::F;
		b;
	}

	henselLift(a:M, inv:MF, b:Vector Z, B:Z): (Vector Z, Z) == {
		n:SI := #b;
		c := copy b;
		pk:Z := 1;
		x:Vector Z := zero n;
		while (pk<B) repeat {
			xk := upgrade(inv*downgrade(c));
--for i in 1..n repeat print << xk(i) << newline;
			x := x+pk*xk;
			c := c-a*xk;
			for i in 1..n repeat c(i) := (integer(c(i)) quo p)::Z;
			pk := pk*(p::Z);
--print << pk << newline << newline;
		}
		(x, pk)
	}

	local ratrecon(u:Z, m:Z, nb:Z, db:Z): Partial Cross(Z,Z) == {
		(s0,t0):Z := (0,1);
		(s1,t1):Z := (m, u rem m);
		while nb<abs(t1) repeat {
			(q, r1) := divide(s1, t1);
			r0 := s0-q*t0;
			(s0, s1) := (t0, t1);
			(t0, t1) := (r0, r1);
		}
		abs(t0)>db => failed;
		[(t1, t0)];
	}


	local norm(a:M): Z == {
		n:SI := rows a;
		max := abs a(1,1);
		for i in 1..n repeat
			for j in 1..n repeat
				if (abs a(i,j))>max then
					max := abs a(i,j);
		max;
	}

	local norm(b:Vector Z): Z == {
		n:SI := #b;
		max := abs b(1);
		for i in 1..n repeat
			if (abs b(i))>max then
				max := abs b(i);
		max;
	}

	local hadamard(a:M): Z == {
		n := (rows a)::I;
		max := norm a;
		even? n ==> ((n^(n quo 2))::Z)*max^n;
		((n^((n quo 2)+1))::Z)*max^n;
	}

	local hadamard(a:M, b:Vector Z): Z == {
		n := (rows a)::I;
		maxa := norm a;
		maxb := norm b;
		even? n ==> ((n^(n quo 2))::Z)*maxa^(n-1)*maxb;
		((n^((n quo 2)+1))::Z)*maxa^(n-1)*maxb;
	}

	henselSolve(a:M, inv:MF, b:Vector Z): (Vector Z, Z) == {
--		import from SI;
--		n := rows a;
--		for i in 1..n repeat {
--			for j in 1..n repeat
--				print << a(i,j) << "  ";
--			print << newline;
--		}
--		for i in 1..n repeat
--			print << b(i) << "  ";
--		print << newline << newline;
		nB := hadamard(a,b);
		dB := hadamard a;
--print << "Bounds" << newline << nB << newline << dB << newline << newline;
		henselSolve(a, inv, b, nB, dB);
	}

	henselSolve(a:M, inv:MF, b:Vector Z, nB:Z, dB:Z): (Vector Z, Z) == {
		import from Q, Cross(Z, Z), Partial Z;

		n:SI := #b;
		c := copy b;
		pk:Z := 1;
		x:Vector Z := zero n;
		xn:Vector Z := zero n;
		xd:Vector Z := zero n;

		xk := upgrade(inv*downgrade(c));
--for i in 1..n repeat print << xk(i) << newline;
		x := x+pk*xk;
		pk := pk*(p::Z);
		q := ratrecon(x(1), pk, nB, dB);

		c := c-a*xk;
		for i in 1..n repeat c(i) := (integer(c(i)) quo p)::Z;
--for i in 1..n repeat print << c(i) << newline;
--print << pk << newline << newline;
		repeat {
			xk := upgrade(inv*downgrade(c));
--for i in 1..n repeat print << xk(i) << newline;
			x := x+pk*xk;
			pk := pk*(p::Z);
			newq := ratrecon(x(1), pk, nB, dB);
			if (~failed? newq) and (~failed? q) then {
				(num, den) := retract q;
				(newnum, newden) := retract newq;
				if (num=newnum) and (den=newden) then {
					xn(1) := num;
					xd(1) := den;
					for i in 2..n while ~failed? q repeat {
						q := ratrecon(x(i), pk, nB, dB);
						if ~failed? q then {
							(num,den) := retract q;
							xn(i) := num;
							xd(i) := den;
						}
					}
					if ~failed? q then {
						denom := xd(1);
						for i in 2..n repeat
							denom := lcm(denom,xd(i));
						for i in 1..n repeat
							xn(i) := xn(i)*(retract(exactQuotient(denom,xd(i))));
						if zero?(a*xn-denom*b) then
							return (xn,denom); 
					}
				}
			}
			q := newq;
			c := c-a*xk;
			for i in 1..n repeat c(i) := (integer(c(i)) quo p)::Z;
--for i in 1..n repeat print << c(i) << newline;
--print << pk << newline << newline;
		}
	}

}

