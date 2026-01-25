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
-------------------------------  hensel.as  ---------------------------------
#include "sumit"

UnivariateHenselLifting(Z:IntegerCategory, P:UnivariatePolynomialCategory0 Z,
	F:Join(FiniteField,SumitField),PF:UnivariatePolynomialCategory0 F):with{
	linearLift:		(P,List PF,Z)		->	Cross(Partial List P,Z);
	linearLift:		(P,F,Z)			->	Cross(Partial Z,Z);
	linearLift:		(P,List F,Z)		->	Cross(Partial List Z,Z);
	upgrade:		PF			->	P;
	downgrade:		P			->	PF;
} == add {
	local p == characteristic$PF;

	upgrade(a:PF):P == {
		import from Z,F;
		r:P := 0;
		p2 := p quo 2;
		for t in a repeat {
			(c,e) := t;
			cc := (lift c)::Z;
			if (integer cc) > p2 then cc := cc-p::Z; 
			r := add!(r,cc,e);
		}
		r;
	}
	
	downgrade(a:P):PF == {
		import from Z,F,Integer;
		r:PF := 0;
		for t in a repeat {
			(c,e) := t;
			r := add!(r, integer(c)::F, e);
		}
		r;
	}

	-- returns g (normalized) and s t s.t. a s + b t = g = gcd(a, b);
	local eea(a:PF,b:PF):(PF,PF,PF) == {
		import from F;
		(c, c1, c2) := extendedEuclidean(a, b);
		ASSERT(c1 * a + c2 * b = c);
		ilc := inv leadingCoefficient c;
		g := ilc * c;
		s := ilc * c1;
		t := ilc * c2;
		ASSERT(s * a + t * b = g);
		ASSERT(one? leadingCoefficient g);
		(g,s,t);
	}

	local diophant(a:PF,b:PF,s1:PF,t1:PF,c:PF):(PF,PF) == {
		s := s1*c;
		t := t1*c;
		(q,sigma) := divide(s,b);
		tau := t + q*a;
		(sigma,tau);
	}

	local diophant(a:PF,b:PF,c:PF):(PF,PF) == {
		(g,s1,t1) := eea(a,b);
		ASSERT(g=1);
		diophant(a,b,s1,t1,c);
	}

	linearLift(f:P, up:PF, vp:PF, bound:Z):Cross(Partial Cross(P,P),Z) == {
		TRACE("linearLift, f = ", f);
		TRACE("up = ", up);
		TRACE("vp = ", vp);
		TRACE("bound = ", bound);
		import from Partial Cross(P,P);
		lc := leadingCoefficient f;
		f := lc*f;
		up := (integer lc)*up; vp := (integer lc)*vp;
		u := upgrade up; v := upgrade vp;
		-- at this point, f - u v = 0 mod p
		-- u := u-monomial(leadingCoefficient u,degree u)+monomial(lc,degree u);
		u := setCoefficient!(u, degree u, lc);
		TRACE("u = ", u);
		-- v := v-monomial(leadingCoefficient v,degree v)+monomial(lc,degree v);
		v := setCoefficient!(v, degree v, lc);
		TRACE("v = ", v);
		e := f-u*v;
		TRACE("e = ", e);
		(g,s1,t1) := eea(vp,up);
		TRACE("gcd(vp,up) = ", g);
		TRACE("coeff_vp = ", s1);
		TRACE("coeff_up = ", t1);
		~one? g => (failed,p::Z);
		ASSERT(one? g);
		i:Integer := 1;
		modulus:Integer := p;
		while modulus < (integer bound) and (e~=0) repeat {
			import from Partial P;
			TRACE("lifting to p^",i);
#if TRIALDIV
			{ -- trial division
				import from Partial P;
				tq := exactQuotient(f,u);
				~failed? tq => {
					TRACE("trial division succeeded on 1st factor");
					return (u,retract tq);
				}
				tq := exactQuotient(f,v);
				~failed? tq => {
					TRACE("trial division succeeded on 2nd factor");
					return (retract tq,v);
				}
			}
#endif
			c0 := exactQuotient(e,modulus::P);
			failed? c0 => return (failed,modulus::Z);
			c := retract c0;
			if c=0 then {
				du:P := 0; dv:P := 0;
			}
			else {
				TRACE("solving diophantine equation","");
				(dU,dV) := diophant(vp,up,s1,t1,downgrade c);
				du := upgrade dU; dv := upgrade dV;
			}
			TRACE("updating error term","");
			e := e - modulus*(v*du + u*dv) - (modulus*modulus*(du*dv));
			u := u+modulus*du; v := v+modulus*dv;
			i := next i;
			modulus := modulus * p;
		}
		([(primitivePart u,primitivePart v)],modulus::Z);
	}
	
	linearLift(f:P, lp:List PF, bound:Z):Cross(Partial List P,Z) == {
		TRACE("linearLift, f = ", f);
		TRACE("lp = ", lp);
		TRACE("bound = ", bound);
		import from List PF,SingleInteger,Partial List P,
				Partial Cross(P,P),List P;
		if #lp=2 then {
			(r,liftk) := linearLift(f,lp(1),lp(2),bound);
			failed? r => return (failed,p::Z);
			(u,v) := retract r;
			return ([[u,v]],liftk);
		}
		up := first lp; lp := rest lp;
		vp:PF := 1;
		for t in lp repeat vp := vp * t;
		(r,k1) := linearLift(f,up,vp,bound);
		liftk := k1;
		failed? r => return (failed,liftk);
		(u,v) := retract r;
		(l,k2) := linearLift(v,lp,bound);
		if liftk<k2 then liftk := k2;
		failed? l => return (failed,liftk);
		([cons(u, retract l)],liftk);
	}

	linearLift(f:P, u:F, bound:Z):Cross(Partial Z,Z) == {
		TRACE("linearLift, f = ", f);
		TRACE("u = ", u);
		TRACE("bound = ", bound);
		import from PF,Partial Z;
		df := differentiate f;
		dfp := downgrade df;
		TRACE("derivative: ",dfp);
		denom := dfp(u);
		denom = 0 => return (failed,p::Z);
		ASSERT(denom ~= 0);
		U := (lift u)::Z;
		ASSERT((downgrade f)(u)=0);
		p2 := p quo 2;
		if (integer U) > p2 then U := U - p::Z;
		i:Integer := 1;
		modulus:Integer := p;
		while modulus < (integer bound) and f(U) ~= 0 repeat {
			TRACE("lifting to p^",i);
			q := exactQuotient(f(U),modulus::Z);
			failed? q => return (failed,modulus::Z);
			qo := q::Z;
			qq := integer(qo)::F;
			if qq ~= 0 then {
				du := - qq / denom;
				dU := (lift du)::Z;
				if (integer dU) > p2 then dU := dU - p::Z;
				U := U + dU * modulus::Z;
			}
			i := next i;
			modulus := modulus * p;
		}
		(U::(Partial Z),modulus::Z);
	}

	linearLift(f:P, ul:List F, bound:Z):Cross(Partial List Z,Z) == {
		TRACE("linearLift, f = ", f);
		TRACE("ul = ", ul);
		TRACE("bound = ", bound);
		import from Partial Z,Partial List Z;
		r:List Z := empty();
		liftk:Z := -1;
		for u in ul repeat {
			(l,k1) := linearLift(f,u,bound);
			if k1>liftk then liftk := k1;
			failed? l => return (failed,liftk);
			r := cons( l::Z, r);
		}
		r := reverse! r;
		(r::(Partial List Z),liftk);
	}
}

