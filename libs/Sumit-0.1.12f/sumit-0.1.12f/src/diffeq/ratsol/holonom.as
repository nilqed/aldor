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
------------------------------ holonom.as --------------------
-- Copyright Manuel Bronstein, 1998
-- Copyright INRIA, 1998

#include "sumit"

#if ASDOC
#endif

macro {
	I	== SingleInteger;
	Z	== Integer;
	Q	== Quotient Z;
	ARR	== PrimitiveArray;
	QR	== RationalRoot;
	SING	== PlaneSingularity(R, Rx);
	PS	== Record(ctr:Rx, reg?:Boolean, drp:Z, nrat:Z,
					ratexp: List QR, slp: List Q);
	HEQ	== Record(op:Rxd, finsing:List SING, infsing:Partial SING,
					todo:Rx, infdone?:Boolean, infDrop:Z);
	Rxe	== LinearOrdinaryDifferenceOperator(R, Rx);
	Qx	== Quotient Rx;
	M	== DenseMatrix;
	FX	== SparseUnivariatePolynomial F;
	Fx	== Quotient FX;
	Fxd	== LinearOrdinaryDifferentialOperator Fx;
	QmZ	== SetsOfRationalsModuloZ;
}

SetsOfRationalsModuloZ: AbelianMonoid with {
	+: (Q, %) -> %;
	*: (Z, %) -> %;
	generator: % -> Generator Q;
	minInteger: % -> Partial Z;
} == add {
	macro Rep == List Q;
	import from Rep;

	0:%				== per empty();
	zero?(s:%):Boolean		== empty? rep s;
	generator(s:%):Generator Q	== generator rep s;
	(p:TextWriter)<<(t:%):TextWriter== p << rep t;

	(s:%) = (t:%):Boolean == {
		for q in s repeat ~member?(q, t) => return false;
		for q in t repeat ~member?(q, s) => return false;
		true;
	}

	local member?(q:Q, t:%):Boolean == {
		import from Z;
		for s in t repeat one? denominator(s - q) => return true;
		false;
	}

	(q:Q) + (t:%):% == {
		import from Z;
		TRACE("QmodZ::*: q = ", q);
		TRACE("QmodZ::*: t = ", t);
		for s in t repeat {
			n := s - q;
			n <= 0 and one? denominator n => return t;
		}
		TRACE("QmodZ::*: adding ", q);
		per cons(q, rep t);
	}

	(s:%) + (t:%):% == {
		import from Q;
		TRACE("QmodZ::+: s = ", s);
		TRACE("QmodZ::+: t = ", t);
		l:% := 0;
		for r in s repeat for q in t repeat l := (r + q) + l;
		TRACE("QmodZ::+: l = ", l);
		l;
	}

	(m:Z) * (s:%):% == {
		ASSERT(m > 0);
		TRACE("QmodZ::*: m = ", m);
		TRACE("QmodZ::*: s = ", s);
		one? m or zero? s => s;
		t := (m quo 2) * s;
		TRACE("QmodZ::*: t = ", t);
		t := t + t;
		TRACE("QmodZ::*: t = ", t);
		even? m => t;
		s + t;
	}

	minInteger(s:%):Partial Z == {
		import from Z, Q;
		mm:Partial Z := failed;
		for r in s | one? denominator r repeat {
			n := numerator r;
			if failed? mm or n < retract mm then mm := [n];
		}
		mm;
	}
}

PlaneSingularity(R:IntegralDomain, Rx: UnivariatePolynomialCategory R):
	BasicType with {
		center: % -> Rx;
		degreeBound: (%, Vector Qx) -> Z;	-- inhomogeneous case
		degreeBound: (%, m:Z == 1) -> Z;	-- homogeneous case
		drop: % -> Z;
		exponentialDegreeBound: % -> Z;		-- riccatti bound
		-- params are (center, regular?, drop, Q-exponents, slopes)
		finite: (Rx, Boolean, Z, List QR, List Q) -> %;
		finite?: % -> Boolean;
		-- params are (regular?, drop, Q-exponents, slopes)
		infinity: (Boolean, Z, List QR, List Q) -> %;
		irregular?: % -> Boolean;
		maxIntegerSlope: % -> Partial Z;
		minIntegerExponent: (%, m:Z == 1) -> Partial Z;
		numberOfRationalExponents: % -> Z;
		rationalExponents: % -> List QR;
		regular?: % -> Boolean;
} == add {
	-- ctr:Rx		== center of the place
	-- reg?:Boolean		== true if regular singularity
	-- drp:Z		== m such that nu(L y) = m + nu(y) if no cancel
	-- nrat:Z		== number of rational exponents
	-- ratexp: List QR	== rational exponents
	-- slp: List Q		== slopes of the newton polygon
	macro Rep == PS;

	import from Rep;

	(s:%) = (t:%):Boolean	== { import from Rx; center s = center t; }
	finite?(s:%):Boolean	== { import from Rx; ~zero?(center s); }
	center(s:%):Rx				== rep(s).ctr;
	regular?(s:%):Boolean			== rep(s).reg?;
	irregular?(s:%):Boolean			== ~regular?(s);
	rationalExponents(s:%):List QR		== rep(s).ratexp;
	numberOfRationalExponents(s:%):Z	== rep(s).nrat;
	drop(s:%):Z				== rep(s).drp;
	local slopes(s:%):List Q		== rep(s).slp;
	(p:TextWriter) << (s:%):TextWriter	== p << "PlaneSingularity";

	sample:% == {
		import from Z, List Q, List QR;
		infinity(true, 0, empty(), empty());
	}

	infinity(r?:Boolean, n:Z, l:List QR, ls:List Q):% == {
		import from Rx;
		finite(0, r?, n, l, ls);
	}

	finite(p:Rx, r?:Boolean, n:Z, l:List QR, ls:List Q):% ==
		per [p, r?, n, mult l, l, ls];

	local mult(l:List QR):Z == {
		n:Z := 0;
		for q in l repeat n := n + multiplicity q;
		n;
	}

	local infBound(s:%, g:Vector Qx):Z == {
		import from I, Rx, Qx;
		m:Z := 0;
		for i in 1..#g | ~zero?(g.i) repeat {
			d := degree(denominator(g.i)) - degree(numerator(g.i));
			if d < m then m := d;
		}
		m;
	}

	local fBound(p:Rx, g:Vector Qx):Z == {
		import from I, Rx, Qx;
		nu:Rx -> Z := order p;
		m:Z := 0;
		for i in 1..#g | ~zero?(g.i) repeat {
			d := nu(numerator(g.i)) - nu(denominator(g.i));
			if d < m then m := d;
		}
		m;
	}

	-- TEMPORARY: RATHER UGLY AND INEFFICIENT
	local finiteBound(s:%, g:Vector Qx):Z == {
		import from I, Qx, List Rx, Product Rx;
		import from BalancedFactorization(R pretend GcdDomain, Rx);
		m:Z := 0;
		b := balancedFactor(center s,[denominator(g.i) for i in 1..#g]);
		for term in b repeat {
			(a, n) := term;
			d := fBound(a, g);
			if d < m then m := d;
		}
		m;
	}

	degreeBound(s:%, g:Vector Qx):Z == {
		import from I, Rx, Qx;
		m := { finite? s => finiteBound(s, g); infBound(s, g) }
		assert(m <= 0);
		max(degreeBound(s, 1), drop(s) - m);
	}

	degreeBound(s:%, m:Z):Z == {
		import from Partial Z;
		u := minIntegerExponent(s, m);
		failed? u or (k := retract u) > 0 => 0;
		-k;
	}

	exponentialDegreeBound(s:%):Z == {
		import from Partial Z;
		fin? := finite? s;
		failed?(u := maxIntegerSlope s) or (m := retract u) <= 0 => {
			fin? => 1;
			0;
		}
		fin? => next m;
		prev m;
	}

	maxIntegerSlope(s:%):Partial Z == {
		import from Z, Q, List Q;
		m:Partial Z := failed;
		for q in slopes s | one? denominator q repeat {
			n := numerator q;
			if failed? m or n > retract m then m := [n];
		}
		m;
	}

	minIntegerExponent(s:%, m:Z):Partial Z == {
		import from Q, QmZ;
		ASSERT(m > 0);
		one? m => minIntegerExponent1 s;
		l:QmZ := 0;
		for q in rationalExponents s repeat {
			(a, d) := value q;
			l := (a / d) + l;
		}
		minInteger(m * l);
	}

	local minIntegerExponent1(s:%):Partial Z == {
		import from Z, QR, List QR;
		m:Partial Z := failed;
		for q in rationalExponents s | integer? q repeat {
			n := integerValue q;
			if failed? m or n < retract m then m := [n];
		}
		m;
	}
}

HolonomicEquation(R: Join(GcdDomain, RationalRootRing),
	Rx: UnivariatePolynomialCategory R,
	Rxd:LinearOrdinaryDifferentialOperatorCategory Rx): SumitType with {
		allRationalExponents?: % -> Boolean;
		analyze!: (%, Rx) -> List SING;
		analyze!: (%, Product Rx) -> List SING;
		analyzedSingularities: % -> List SING;
		coerce: Rxd -> %;
		dropAtInfinity: % -> Z;
		finiteSingularities: % -> List SING;
		fuchsian?: % -> Boolean;
		operator: % -> Rxd;
		order: % -> Z;
		if R has Specializable then {
			pCurvature: (%, Z) -> Partial M Qx;
#if ASDOC
\aspage{pCurvature}
\Usage{\name(L,p)}
\Signature{(Rxd, Integer)}{Partial DenseMatrix Quotient Rx}
\Params{
{\em L} & Rxd & A differential operator\\
{\em p} & Integer R & A prime\\
}
\Retval{Returns the $p$-curvature of $L$ if the numeric coefficients of $L$ can
be reduced modulo $p$, \failed otherwise.}
\seealso{pCurvature(LinearOrdinaryDifferentialSystem)}
#endif
		}
		singularAtInfinity?: % -> Boolean;
		singularityAtInfinity: % -> Partial SING;
} == add {
	-- op:Rxd		== underlying operator
	-- finsing:List SING	== list of finite singularities
	-- infsing:Partial SING	== singularity at infinity if any
	-- todo:Rx		== singularities still to analyze
	-- infdone?:Boolean	== true when infinity has been analyzed
	-- infDrop:Z		== order drop at infinity (whether sing. or not)
	macro Rep == HEQ;

	sample:%			== { import from Rxd; 1::%; }
	operator(eq:%):Rxd		== { import from Rep; rep(eq).op; }
	local unanalyzed(eq:%):Rx	== { import from Rep; rep(eq).todo; }
	local finite(eq:%):List SING	== { import from Rep; rep(eq).finsing; }
	local inf(eq:%):Partial SING	== { import from Rep; rep(eq).infsing; }
	local drop(eq:%):Z		== { import from Rep; rep(eq).infDrop; }
	order(eq:%):Z			== {import from Rxd;degree operator eq;}
	extree(eq:%):ExpressionTree == { import from Rxd; extree operator eq; }
	finiteSingularities(eq:%):List SING	== finite analyze! eq;
	analyzedSingularities(eq:%):List SING	== finite eq;
	singularityAtInfinity(eq:%):Partial SING== inf analyzeAtInfinity! eq;
	dropAtInfinity(eq:%):Z			== drop analyzeAtInfinity! eq;

	-- n = degree of the differential operator
	local allrat?(n:Z)(s:SING):Boolean == {
		import from Rx;
		m := numberOfRationalExponents s;
		finite? s => m = n * degree center s;
		m = n;
	}

	local analyzedAtInfinity?(eq:%):Boolean	== {
		import from Rep;
		rep(eq).infdone?;
	}

	fuchsian?(eq:%):Boolean	== {
		import from SING;
		all?(analyze! eq, regular?);
	}

	(eq1:%) = (eq2:%):Boolean == {
		import from Rxd;
		operator eq1 = operator eq2;
	}

	local all?(eq:%, test?:SING -> Boolean):Boolean == {
		import from List SING, Partial SING;
		for s in finite eq repeat ~test?(s) => return false;
		failed?(u := singularityAtInfinity eq) or test?(retract u);
	}

	allRationalExponents?(eq:%):Boolean == {
		import from Rxd;
		all?(analyze! eq, allrat? degree operator eq);
	}

	singularAtInfinity?(eq:%):Boolean == {
		import from Partial SING;
		~failed? singularityAtInfinity eq;
	}

	coerce(L:Rxd):%	== {
		import from Rep, Z, Rx, List SING, Partial SING;
		per [L, empty(), failed,
			squareFreePart leadingCoefficient L, false, 0];
	}

	if R has Specializable then {
		pCurvature(eq:%, p:Z):Partial M Qx ==
			pCurvature(operator eq, primeField p);

		local primeField(p:Z):PrimeFieldCategory == {
			import from I;
			ASSERT(p > 0);
			p < 10007 => ZechPrimeField retract p;
			p < 2^16 => SmallPrimeField retract p;
			BigPrimeField p;
		}

		local pCurvature(L:Rxd, F:PrimeFieldCategory):Partial M Qx == {
			import from Partial Fxd;
			import from LinearOrdinaryDifferentialSystem Fx, _
			     System2LinearOrdinaryDifferentialOperator(Fx, Fxd);
			failed?(u := specialize(L, F)) => failed;
			m := pCurvature(companionSystem retract u,
			-- TEMPORARY: NO CONDITIONAL CONSTANTS (969)
							--derivation$Fx);
							derivation()$Fx);
			[lift(F, m)];
		}

		local specialize(L:Rxd, F:PrimeFieldCategory):Partial Fxd == {
			import from I, PartialFunction(R, F);
			s := specialization(F)$R;
			~failed?(u := specialize(L, F, s)) => u;
			-- try a few specializations just in case
			for i in 1..9 repeat {
				t := specialization(F)$R;
				s = t => return failed;
				~failed?(u := specialize(L, F, t)) => return u;
			}
			failed;
		}

		local specialize(L:Rxd, F:PrimeFieldCategory,
					f:PartialFunction(R,F)):Partial Fxd == {
			import from Fx, Partial Fx, Fxd;
			failed?(u := specialize(leadingCoefficient L, F, f))
				or zero?(lc := retract u) => failed;
			Lp := monomial(lc, degree L);
			for term in reductum L repeat {
				(c, n) := term;
				failed?(u:=specialize(c,F,f)) => return failed;
				Lp := add!(Lp, retract u, n);
			}
			[Lp];
		}

		local specialize(p:Rx, F:PrimeFieldCategory,
					f:PartialFunction(R, F)):Partial Fx == {
			import from Partial F, FX, Fx;
			q:FX := 0;
			for term in p repeat {
				(c, n) := term;
				failed?(u:=partialApply(f,c)) => return failed;
				q := add!(q, retract u, n);
			}
			[q::Fx];
		}

		local lift(F:PrimeFieldCategory, mf:M Fx):M Qx == {
			import from I, Fx;
			(r, c) := dimensions mf;
			m:M Qx := zero(r, c);
			for i in 1..r repeat {
				for j in 1..c repeat {
					if ~zero?(a := mf(i,j)) then
						m(i,j) := lift(F, a);
				}
			}
			m;
		}

		local lift(F:PrimeFieldCategory, f:Fx):Qx == {
			lift(F, numerator f) / lift(F, denominator f);
		}

		local lift(F:PrimeFieldCategory, p:FX):Rx == {
			import from F, R;
			q:Rx := 0;
			for term in p repeat {
				(c, n) := term;
				q := add!(q, lift(c)::R, n);
			}
			q;
		}
	}

	-- does not analyze at infinity
	local analyze!(eq:%):% == {
		import from Z, Rx, Rxd, Product Rx, List SING;
		import from BalancedFactorization(R, Rx);
		TRACE("holonom::analyze!, eq = ", eq);
		zero? degree(p := unanalyzed eq) => eq;
		TRACE("::unanalyzed part = ", p);
		f := finite eq;
		TRACE("::finite = ", f);
		L := operator eq;
		for term in balancedFactor(p, coefficients L) repeat {
			(a, n) := term;
			(f, p) := analyze(L, a, f, p);
		}
		set!(eq, f, p);
	}

	-- does not analyze at infinity
	analyze!(eq:%, q:Rx):List SING == {
		import from Z, Rx, Rxd, Product Rx, List SING;
		import from BalancedFactorization(R, Rx);
		f:List SING := empty();
		zero? degree(p := unanalyzed eq)
			or zero? degree(q := gcd(q, p)) => f;
		L := operator eq;
		for term in balancedFactor(q, coefficients L) repeat {
			(a, n) := term;
			(f, p) := analyze(L, a, f, p);
		}
		set!(eq, concat(finite eq, f), p);
		f;
	}

	-- does not analyze at infinity
	analyze!(eq:%, places:Product Rx):List SING == {
		import from Z, Rx, Rxd, Product Rx, List SING;
		import from BalancedFactorization(R, Rx);
		f:List SING := empty();
		zero? degree(p := unanalyzed eq) => f;
		coeffs := coefficients(L := operator eq);
		for term in places repeat {
			(a, n) := term;
			a := gcd(a, p);
			if degree(a) > 0 then {
				for trm in balancedFactor(a, coeffs) repeat {
					(a, n) := trm;
					(f, p) := analyze(L, a, f, p);
				}
			}
		}
		set!(eq, concat(finite eq, f), p);
		f;
	}

	local analyze(L:Rxd, a:Rx, l:List SING, p:Rx):(List SING, Rx) == {
		import from Z, List QR, List Q;
		ASSERT(~zero? a);
		(d := degree a) > 0 => {
			(reg?, drp, exp, slp) := ratexpon(L, a, d);
			TRACE("analyze::reg? = ", reg?);
			TRACE("analyze::drp = ", drp);
			TRACE("analyze::exp = ", exp);
			TRACE("analyze::slp = ", slp);
			(cons(finite(a,reg?,drp,exp,slp), l), quotient(p, a));
		}
		(l, p);
	}

	local analyzeAtInfinity!(eq:%):% == {
		import from SING, Partial SING;
		analyzedAtInfinity? eq => eq;
		(ord?, reg?, drp, exp, slp) := ratexpon operator eq;
		-- store the order drop whether the equation is singular or not
		set!(eq, { ord? => failed; [infinity(reg?,drp,exp,slp)] }, drp);
	}

	local set!(eq:%, f:List SING, p:Rx):% == {
		import from Rep;
		rep(eq).finsing := f;
		rep(eq).todo := p;
		eq;
	}

	local set!(eq:%, s:Partial SING, n:Z):% == {
		import from Rep;
		rep(eq).infsing := s;
		rep(eq).infdone? := true;
		rep(eq).infDrop := n;
		eq;
	}

	-- checks whether a is a regular singularity
	-- and computes all the rational exponents
	-- as well as the slopes and the order drop
	-- returns (regular?, drop, Q-exponents, slopes)
	local ratexpon(L:Rxd, a:Rx, d:Z):(Boolean, Z, List QR, List Q) == {
		import from  R;
		ASSERT(~zero? a); ASSERT(unit? content a);
		ASSERT(d = degree a); ASSERT(d > 0);
		TRACE("holonom::ratexpon, L = ", L);
		TRACE("::a = ", a);
		TRACE("::d = ", d);
		one? d => ratexpon1(L, a);
		unit?(lc := leadingCoefficient a) =>
			ratexpon(L, UnivariatePolynomialMod(R, Rx, a),
							AffinePlace(R, Rx, a));
		ratexponNL(L, lc, a, d);
	}

	macro {
		Ra  == QuotientBy(R, lc, false);
		Rax == SparseUnivariatePolynomial Ra;
	}

	-- case where a is nonlinear and its leadingCoeff lc is not a unit in R
	local ratexponNL(L:Rxd,lc:R,a:Rx,d:Z):(Boolean, Z, List QR, List Q) == {
		import from Ra, Rax;
		ASSERT(~unit? lc); ASSERT(d = degree a); ASSERT(d > 1);
		TRACE("holonom::ratexponNL, L = ", L);
		TRACE("::lc = ", lc);
		TRACE("::a = ", a);
		TRACE("::d = ", d);
		q:Rax := monomial(1, d);	-- q will be a / lc
		for term in reductum a repeat {
			(c, n) := term;
			q := add!(q, shift(c::Ra, -1), n);
		}
		TRACE("::q = ", q);
		ratexponNL(L, lc, a, q);
	}

	-- needed just in order to create a scope in which b is constant
	local ratexponNL(L:Rxd,lc:R,a:Rx,b:Rax):(Boolean, Z, List QR, List Q) ==
		ratexpon(L, UnivariatePolynomialMod(Ra, Rax, b),
				AffinePlace1(R, Rx, a, Ra, Rax, b));

	-- case where a has degree 1, its root may or may not be in R
	local ratexpon1(L:Rxd, a:Rx):(Boolean, Z, List QR, List Q) == {
		import from R, Partial R;
		ASSERT(one? degree a);
		a1 := leadingCoefficient a;
		a0 := - coefficient(a, 0);
		u := exactQuotient(a0, a1);
		failed? u => ratexpon1(L, a1, a0);
		ratexpon(L, R, RationalPlace(R, Rx, retract u));
	}

	-- case where we are localizing at b/a and b/a is not in R
	local ratexpon1(L:Rxd, a:R, b:R):(Boolean, Z, List QR, List Q) == {
		ASSERT(~zero? a); ASSERT(~unit? a); ASSERT(unit? gcd(a, b));
		ratexpon(L, QuotientBy(R, a, false), RationalPlace1(R,Rx,a,b));
	}

	local ratexpon(L:Rxd, S:Join(CommutativeRing, RationalRootRing),
		P:DifferentialPlace(Rx, S)):(Boolean, Z, List QR, List Q) == {
		import from LinearOrdinaryDifferentialNewtonPolygon(Rx,S,P,Rxd);
		TRACE("holonom::ratexpon, L = ", L);
		N := newtonPolygon L;
		TRACE("::newton polygon ", "computed");
		(regular? N, orderDrop N, rationalExponents N, slopes N);
	}

	local ratexpon(L:Rxd):(Boolean, Boolean, Z, List QR, List Q) == {
		import from LinearOrdinaryDifferentialNewtonPolygon(Rx, R,
						RationalInfinity(R, Rx), Rxd);
		N := newtonPolygon L;
		(ordinary? N, regular? N, orderDrop N,
						rationalExponents N, slopes N);
	}
}


HolonomicRecurrence(R:CommutativeRing,
	Rx:UnivariatePolynomialCategory R): SumitType with {
		coerce: Rxe -> %;
		degree: % -> Z;
		if R has Field then fill!: % -> (ARR R,I,I,Boolean) -> List I;
		operator: % -> Rxe;
		reductum: % -> (ARR R, I) -> R;
		shift: (Rxe, Z) -> %;
		trailingDegree: % -> Z;
	} == add {
		-- The recurrence is stored as R(E) E^e
		-- where the coefficient of degree 0 of R(E) is nonzero.
		macro Rep == Record(oper:Rxe, exponent:Z);

		local field?:Boolean	== R has Field;
		sample:%		== { import from Rxe; 1::%; }
		coerce(L:Rxe):%		== { import from Z; shift(L, 0); }
		degree(L:%):Z		== { import from Rxe;degree operator L;}
		trailingDegree(L:%):Z	== { import from Rep; rep(L).exponent; }
		operator(L:%):Rxe	== { import from Rep; rep(L).oper;}
		local recur(L:Rxe,n:Z):%== { import from Rep; per [L, n]; }

		extree(L:%):ExpressionTree == {
			import from Rxe;
			extree operator L;
		}

		(L1:%) = (L2:%):Boolean == {
			import from Z, Rxe;
			operator L1 = operator L2
				and trailingDegree L1 = trailingDegree L2;
		}

		-- return L(E) E^n
		shift(L:Rxe, n:Z):% == {
			(a, e) := trailingMonomial L;
			if e > 0 then L := shft(L, -e);
			recur(L, e + n);
		}

		-- return L(E) E^n
		local shft(L:Rxe, n:Z):Rxe == {
			s:Rxe := 0;
			for term in L repeat {
				(c, e) := term;
				ASSERT(0 <= e + n);
				s := add!(s, c, e + n);
			}
			s;
		}

		-- returns the dot product
		-- (c.1(n),...,c.nu(n)) . (a_m,...,a_(m+nu-1))
		-- where a_i is stored in a[i]
		local dot(c:ARR Rx, n:R, a:ARR R, m:I, nu:I):R == {
			import from Rx;
			ans:R := 0;
			start := 1 - min(m, 0);
			for i in start..nu repeat {
				aa := a(m+i);
				if ~(zero? aa) then
					ans := add!(ans, (c.i)(n) * aa);
			}
			ans;
		}

		-- reductum and denom return m and d such that
		-- a_N = -m/d, assuming that a_i is stored in a[i+1]
		reductum(rec:%):(ARR R, I) -> R == {
			import from I, Z, Rxe, ARR Rx;
			nu:I := retract degree rec;
			c:ARR Rx := new(nu, 0);
			for term in reductum operator rec repeat {
				(cf, e) := term;
				c(retract next e) := cf;
			}
			B := nu + retract trailingDegree rec;
			(a:ARR R, N:I):R +-> {
				ASSERT(N >= B);
				dot(c, (N - B)::R, a, N - nu, nu);
			}
		}

		local denom(rec:%):I -> R == {
			import from Z, Rx, Rxe;
			p := leadingCoefficient operator rec;
			B := retract(degree rec + trailingDegree rec);
			(N:I):R +-> p((N-B)::R);
		}

		if R has Field then {
			-- TEMPORARY: 1.1.10a COMPILER INFERENCE BUG
			local dv(a:R, b:R):R == a / b;

			-- compute a_frm to a_two using L
			-- a_0 is the first value, which is stored in a[1]
			-- stores a 0 when a singularity is encountered
			-- returns an empty list if the last argument is false,
			-- all the indices N for which N - B is a singularity
			-- otherwise
			fill!(rec:%):(ARR R, I, I, Boolean) -> List I == {
				num := reductum rec;
				den := denom rec;
				(a:ARR R, frm:I, two:I, s?:Boolean):List I +-> {
					import from R;
					l:List I := empty();
					for N in frm..two repeat {
						if zero?(d := den N) then {
							a(next N) := 0;
							if s? then l:=cons(N,l);
						}
						else a(next N):=dv(-num(a,N),d);
					}
					l;
				}
			}
		}
}
