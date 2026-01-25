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
----------------------------- sit_upmod.as ---------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I	== MachineInteger;
	Z	== Integer;
	Dx	== DenseUnivariatePolynomial(R, avar);
	Dxy	== DenseUnivariatePolynomial Dx;
	ARR	== PrimitiveArray;
}

local UnivariatePolynomialModTools(R:CommutativeRing,
			Rx: UnivariatePolynomialCategory0 R,
			Ry: UnivariatePolynomialCategory0 R,
			Ryz: UnivariatePolynomialCategory0 Ry): with {
	change: Rx -> Ry;
	invmodn: (Rx, Z, R) -> Ry;
	upgrade: Ry -> Ryz;
} == add {
	change(p:Rx):Ry == {
		q:Ry := 0;
		for term in p repeat {
			(c, e) := term;
			q := add!(q, c, e);
		}
		q;
	}

	upgrade(p:Ry):Ryz == {
		q:Ryz := 0;
		for term in p repeat {
			(c, e) := term;
			q := add!(q, c::Ry, e);
		}
		q;
	}

	-- returns a = a0 + a1 x + ... + a_{n-1} a^{n-1}
	-- such that p a = 1 + O(x^{n+1})
	-- n must be degree p and invtc the inverse of p(0)
	invmodn(p:Rx, n:Z, invtc:R):Ry == {
		import from Boolean;
		assert(~zero? p);
		assert(n = degree p);
		assert(one?(invtc * coefficient(p, 0)));
		q := add!(monomial(1, n)$Ry, invtc, 0@Z);	-- x^n + 1/p(0)
		for i in 1..prev n repeat
			q := add!(q, - convolution(p, q, i), i);
		add!(q, -1, n);				-- remove the extra x^n
	}

	-- returns p_1 q_{n-1} + p_2 q_{n-2} + ... + p_n q_0
	local convolution(p:Rx, q:Ry, n:Z):R == {
		c:R := 0;
		for i in 1..n repeat
			c := add!(c, coefficient(p, i) * coefficient(q, n - i));
		c;
	}
}


#if ALDOC
\thistype{UnivariatePolynomialMod}
\History{Manuel Bronstein}{22/6/94}{created}
\History{Manuel Bronstein}{27/7/98}{added Brent-Kung modular composition}
\Usage{
import from \this(R, Rx, p)\\
import from \this(R, Rx, p, x)\\
}
\Params{
{\em R} & \astype{CommutativeRing} & The coefficient ring of the polynomials\\
{\em Rx} & \astype{UnivariatePolynomialCategory0} R & The type of the modulus\\
{\em p} & Rx & The modulus\\
{\em x} & \astype{Symbol} & The generator name (optional)\\
}
\Descr{\this(R, Rx, p) implements the univariate polynomials
modulo $p$, \ie the ring $Rx / (p)$, where $p$ is not necessarily irreducible.
However, the leading coefficient of $p$ must be a unit in R.
Use \astype{SimpleAlgebraicExtension} for extensions where the
modulus is known to be irreducible.}
\begin{exports}
\category{\astype{UnivariatePolynomialQuotient}(R, Rx)}\\
\end{exports}
#endif

UnivariatePolynomialMod(R:CommutativeRing, Rx: UnivariatePolynomialCategory0 R,
	modulus:Rx, avar:Symbol==new()): UnivariatePolynomialQuotient(R,Rx) == {
	-- sanity check on the parameters
	import from I, Z;
	N:I == machine(degree(modulus)$Rx);
	assert(N > 0);
	assert(unit?(leadingCoefficient(modulus)$Rx)$R);

	add {
	Rep == Dx;

	import from Z, Rep, R, Dxy, UnivariatePolynomialModTools(R,Rx,Dx,Dxy);

	-- modulus seen as a dense poly
	local densemod:Dx		== change modulus;

	-- sum_ai y^i where mod = sum_ai x^i
	local modxy:Dxy			== upgrade densemod;

	-- inverse of the leading coefficient of the modulus
	local invlc:R == {
		import from Partial R;
		retract reciprocal(leadingCoefficient(modulus)$Rx);
	}

	local eucdom?:Boolean		== Dx has EuclideanDomain;
	local intdom?:Boolean		== R has IntegralDomain;
	local gcddom?:Boolean		== R has GcdDomain;
	local finiteChar?:Boolean	== R has FiniteCharacteristic;
	local field?:Boolean		== R has Field;
	local fring?:Boolean		== R has FactorizationRing;

	0				== per(0$Rep);
	1				== per(1$Rep);
	(p:%) + (q:%):%			== per(rep p + rep q);
	minus!(p:%):%			== per minus! rep p;
	add!(p:%, q:%):%		== per add!(rep p, rep q);
	coerce(r:R):%			== per monomial(r, 0);
	times!(p:%, q:%):%		== reduce! times!(rep p, rep q);
	(r:R) * (p:%):%			== per(r * rep p);
	characteristic:Z		== characteristic$R;
	(p:%) = (q:%):Boolean		== rep p = rep q;
	-(p:%):%			== per(- rep p);
	coerce(n:Z):%			== per(n::Rep);
	-- coerce(n:I):%			== per(n::Rep);
	extree(p:%):ExpressionTree	== extree rep p;
	copy(p:%):%			== per copy rep p;
	copy!(p:%, q:%):%		== per copy!(rep p, rep q);
	local degext:Z			== N::Z;
	reduce(p:Rx):%			== reduce! change p;
	definingPolynomial:Rx		== modulus;

	-- conditions on which fast reduction via multiplication can be done
	local fftred?:Boolean ==
		R has FFTRing and fftCutoff$(R pretend FFTRing) > 0
			and N > fftCutoff$(R pretend FFTRing);

	-- for fast division: a rem modulus = a - q modulus
	-- where q = (a modbar) quo x^{degext + degree(modbar)}
	local modbar:Dx	== {
		fftred? => revert invmodn(revert modulus, degext, invlc);
		0;
	}
	local cutoffext:Z == { fftred? => degext + degree modbar; 0 }

	local multred!(p:Dx):% == {
		assert(~zero? p);
		assert(degree p >= degext);
		assert(degree p < 2 * degext);
		TRACE("upmod::multred: p = ", p);
		TRACE("upmod::multred: modulus = ", modulus);
		TRACE("upmod::multred: modbar = ", modbar);
		prod := p * modbar;
		d := degree prod - cutoffext;
		q:Dx := 0;
		-- compute the quotient - (p modbar) / x^cutoffext
		for term in prod while d >= 0 repeat {
			(c, e) := term;
			d := e - cutoffext;
			if d >= 0 then q := add!(q, -c, d);
		}
		p := add!(p, densemod * q);
		assert(degree p < degext);
		per p;
	}

	(p:%) * (q:%):% == {
		zero? p or zero? q => 0;
		one? p => q;
		one? q => p;
		reduce!(rep p * rep q);
	}

	-- modular composition by Brent & Kung
	compose(h:%):% -> % == {
		zero? h => { (g:%):% +-> coefficient(rep g, 0)::% };
		h = reduce(monom$Rx) => { (g:%):% +-> g };
		import from ARR Dx;
		(ignore?, t) := nthRoot(N, 2);	-- t^2 <= N < (t+1)^2
		k := N quo t;
		if (t * k) = N then k := prev k;
		hi:ARR Dx := new t;
		hi.0 := 1;
		w:% := 1;
		for i in 1..prev t repeat {
			w := h * w;
			hi.i := rep w;
		}
		ht := h * w;		-- h^t
		(g:%):% +-> {		-- uses Horner's rule at h^t
			zero? g => 0;
			p := rep g;
			v := eval(p, k, t, hi);
			-- TEMPORARY: LOOP-INLINING BUG 1203
			-- for i in prev(k) .. 0 by -1 repeat {
			i := prev k; while i >= 0 repeat {
				v := add!(times!(v, ht), eval(p, i, t, hi));
				i := prev i;
			}
			v;
		}
	}

	-- computes \sum_{j=0..t-1} coeff(p, k t + j) h^j
	-- where h^j is stored in h.j
	-- complexity is O(N t) +/* in R
	local eval(p:Dx, k:I, t:I, h:ARR Dx):% == {
		kt := k * t;
		ans:Dx := 0;
		for j in 0..prev t repeat
			ans := add!(ans, coefficient(p, (kt + j)::Z), h.j);
		per ans;
	}

	exactQuotient(p:%, q:%):Partial % == {
		import from Partial Rep;
		assert(~zero? q);
		zero? p => [0];
		u := {
			eucdom? => diophant(rep q, rep p, densemod);
			intdom? => resdiophant(rep q, rep p);
			-- TEMPORARY: THIS IS OF COURSE WRONG!
			exactQuotient(rep p, rep q);
		}
		failed? u => failed;
		[per retract u];
	}

	if R has IntegralDomain then {
		-- returns z s.t. a z = b mod(modulus)
		local resdiophant(a:Dx, b:Dx):Partial Dx == {
			import from Resultant(R pretend IntegralDomain, Dx);
			assert(~zero? a); assert(~zero? b);
			assert(degree a <= degree densemod);
			-- r = s modulus + t a, so  a (t b / r) = b (mod c)
			(r, s, t) := extendedLastSPRS(densemod, a);
			exactQuotient(rep reduce!(t * b), r);
		}
	}

	if Dx has EuclideanDomain then {
		-- returns z s.t. a z = b mod(c)
		local diophant(a:Dx,b:Dx,c:Dx):Partial Dx == diophantine(a,b,c);
	}

	local reduce!(p:Dx):% == {
		zero? p => 0;
		degree p < degext => per p;
		fftred? => multred! p;
		reduce!(p, densemod, invlc, degext);
	}

	-- classical polynomial division by dmod
	local reduce!(p:Dx, dmod:Dx, ilc:R, deg:Z):% == {
		import from Boolean;
		assert(deg = degree dmod);
		assert(one?(ilc * leadingCoefficient dmod));
		while ~zero? p repeat {
			dp := degree p;
			(d := dp - deg) < 0 => return per p;
			c := ilc * leadingCoefficient p;
			p := add!(p, -c, d, dmod);
		}
		0;
	}

	lift(p:%):Rx == {
		ans:Rx := 0;
		for term in rep p repeat {
			(c, n) := term;
			ans := add!(ans, c, n);
		}
		ans;
	}

	(p:%)^(n:Z):% == {
		import from BinaryPowering(%, Z);
		assert(n >= 0);
		finiteChar? => charpow(p, n);
		zero? n => 1; one? n => p;
		binaryExponentiation!(copy p, n);
	}

	-- TEMPORARY: THESE CONSTANTS SHOULD ONLY BE DEFINED IF R has FRing
	local NFactors:ARR I == new(1, 0);
	local nfactModulus():I == NFactors.1;
	local factModulus:ARR Dx == new N;

	-- TEMPORARY: THIS CONSTANT SHOULD ONLY BE DEFINED IN char p > 0
	local alphap:ARR Rep == new(prev N, 0);

	if R has FiniteCharacteristic then {
		pthPower!(p:%):%	== pthPower p;
		local charpow(p:%,n:Z):%== pExponentiation(p, n)$PthPowering(%);

		-- stores the powers a^p, a^{2p},...,a^{(n-1)p}
		local initPowerTable():() == {
			zero?(alphap.0) => {
				lastxp:% := 1;
				xp := reduce(monomial(1, characteristic$R)$Rx);
				-- TEMPORARY: LOOP-INLINING BUG 1203
				-- for i in 0..prev prev N repeat {
				i:I := 0; while i < prev N repeat {
					lastxp := xp * lastxp;
					alphap.i := rep lastxp;
					i := next i;
				}
			}
		}

		pthPower(p:%):% == {
			import from ARR Rep;
			zero? p or one? p => p;
			initPowerTable();
			q:Rep := 0;
			for term in rep p repeat {
				local c:R; local n:Z;
				(c, n) := term;
				cp := pthPower c;
				if zero? n then q := add!(q, cp, n);
				else q := add!(q, cp, alphap prev machine n);
			}
			per q;
		}
	}

	if R has RationalRootRing then {
		macro RR == FractionalRoot Z;
		macro UPC0 == UnivariatePolynomialCategory0(% pretend CommutativeRing);

		local norm(P:UPC0, p:P):Dx == {
			TRACE("upmod::norm, p = ", p);
			q:Dxy := 0;
			for term in p repeat {
				(calpha, n) := term;
				for aterm in rep calpha repeat {
					(c, m) := aterm;
					q := add!(q, monomial(c, n), m);
				}
			}
			TRACE("upmod::norm, q = ", q);
			TRACE("upmod::norm, modxy = ", modxy);
			resultant(q, modxy);
		}

		-- make p monic if it is possible, return p otherwise
		local normalize(P:UPC0, p:P):P == {
			TRACE("upmod::normalize, p = ", p);
			import from Partial %;
			zero? p => p;
			a := leadingCoefficient p;
			q:P := monomial(1, degree p);
			for term in reductum p repeat {
				(c, n) := term;
				failed?(u := exactQuotient(c, a)) => return p;
				q := add!(q, retract u, n);
			}
			TRACE("upmod::normalize, returning ", q);
			q;
		}

		-- takes only the coefficients of alpha^m
		local project(P:UPC0, p:P, m:Z):Dx == {
			q:Dx := 0;
			for term in p repeat {
				(c, n) := term;
				q := add!(q, coefficient(rep c, m), n);
			}
			q;
		}

		if R has GcdDomain then {
			-- returns the gcd of all the projection
			local gcdproject(P:UPC0, p:P):Dx == {
				assert(~zero? p);
				q:Dx := 0;
				for i in 0..prev N repeat
					q := gcd(q, project(P, p, i::Z));
				q;
			}
		}

		-- returns the gcd of the coeffs if Rx is a Gcd domain,
		-- the first nonzero projection otherwise
		local project(P:UPC0, p:P):Dx == {
			zero? p => 0;
			-- TEMPORARY: WOULD LIKE TO CACHE THE TEST
			-- gcddom? => gcdproject(P, p);
			R has GcdDomain => gcdproject(P, p);
			for i in 0..prev N repeat
				~zero?(q := project(P, p, i::Z)) => return q;
			never;
		}

		-- reduces the coefficients of p modulo q and then projects
		local project(P:UPC0, p:P, q:Dx):Dx == {
			import from Partial R;
			pp:P := 0;
			dq := degree q;
			ilcq := retract(reciprocal(leadingCoefficient(q)$Dx));
			for term in p repeat {
				(c, e) := term;
				pp := add!(pp,
					reduce!(change lift c, q, ilcq, dq), e);
			}
			project(P, pp);
		}

		integerRoots(P:UPC0):P -> Generator RR ==
			(p:P):Generator(RR) +-> roots(P, p, integerRoots$Dx);

		rationalRoots(P:UPC0):P -> Generator RR ==
			(p:P):Generator(RR) +-> roots(P, p, rationalRoots$Dx);

		local roots(P:UPC0, p:P, f:Dx -> Generator RR):Generator RR == {
			import from RR;
			ll:List RR := empty;
			nroot:Z := 0;
			val := value P;
			for rt in f project(P, p) repeat {
				(n, d) := value rt;
				if zero? val(p, n, d) then {
					ll := cons(rt, ll);
					nroot := nroot + multiplicity rt;
				}
			}
			nroot = degree p => generator ll;
			-- TEMPORARY: should deflate p
			fring? => frroots(P, p, f, ll);
			f norm(P, normalize(P, p));
		}

		if R has FactorizationRing then {
			local factorModulus():() == {
				import from Product Dx;
				TRACE("upmod::factormodulus: mod = ", densemod);
				(c, prd) := factor(Dx)(densemod);
				NFactors.0 := #prd;
				TRACE("::number of factors = ", nfactModulus());
				assert(nfactModulus() <= N);
				for t in prd
					for i in 0..prev nfactModulus() repeat {
						(q, e) := t;
						if i = 0 then q := c * q;
						factModulus.i := q;
						TRACE("::factor = ", q);
				}
			}

			-- projects on all the factors
			local frroots(P:UPC0, p:P, f:Dx -> Generator RR,
				l:List RR):Generator RR == {
				import from I, List Dx;
				if nfactModulus() = 0 then factorModulus();
				nfactModulus() = 1 => generator l;
				ll:List RR := empty;
				-- TEMPORARY: LOOP-INLINING BUG 1203
				-- for i in 0..prev nfactModulus() repeat {
				i:I := 0; while i < nfactModulus() repeat {
					ll := merge(ll,
						f project(P, p, factModulus.i));
					i := next i;
				}
				generator ll;
			}

			local find(r:RR, l:List RR):Partial RR == {
				(n, d) := value r;
				for rt in l repeat {
					(a, b) := value rt;
					a*d = b*n => return [rt];
				}
				failed;
			}

			local merge(l1:List RR, l2:Generator RR):List RR == {
				import from RR;
				for rt in l2 repeat {
					(l:List RR, ignore:I) := find(rt, l1);
					if empty? l then l1 := cons(rt, l1);
					else {
						r := first l;
						assert(r = rt);
						setMultiplicity!(r,
							multiplicity r +
							multiplicity rt);
					}
				}
				l1;
			}
		}
	}
	}
}
