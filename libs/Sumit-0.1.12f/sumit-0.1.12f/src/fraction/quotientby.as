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
------------------------ quotientby.as ---------------------------
#include "sumit"

macro Z == Integer;

#if ASDOC
\thistype{QuotientBy}
\History{Manuel Bronstein}{7/6/96}{created}
\Usage{import from \this(R, p, irr?)}
\Params{
{\em R} & IntegralDomain & an integral domain\\
{\em p} & R & a nonzero nonunit of R\\
{\em irr?} & Boolean & Indicates whether p is known to be irreducible in R\\
}
\Descr{
\this(R, p, irr?) forms the quotient of the integral domain {\em R} by the
nonzero nonunit {\em p}, \ie the set of all fractions whose denominator is a
power of {\em p}. Quotients are normalized in the sense that {\em p}
does not divide the numerators. Indicating whether {\em p} is
irreducible if for efficiency purposes only, always use \false~when
it is unknown.
}
\begin{exports}
\category{QuotientByCategory R}\\
\end{exports}
#endif

QuotientBy(R: IntegralDomain, p:R, irr?:Boolean): QuotientByCategory R == {
	-- sanity checks on the parameters
	ASSERT(~zero? p);
	ASSERT(~unit? p);

	add {
	-- Keeps normalized, ie exactQuotient(Numerator, p) = failed
	-- value is Numerator p^Order
	macro Rep == Record(Numerator:R, Order:Z);
	import from Rep;

	local gcd?:Boolean		== R has GcdDomain;
	local mkquot(a:R, n:Z):%	== per [a, n];
	0:%				== mkquot(0, 0);
	1:%				== mkquot(1, 0);
	coerce(a:R):%			== canon(a, 0);
	order(x:%):Z			== rep(x).Order;
	local numord(x:%):(R, Z)	== explode rep x;
	local orderpquo: R -> (Z, R)	== orderquo p;

	random():% == {
		import from Z, R, RandomNumberGenerator;
		canon(random(), (randomInteger() rem 101) - 50);
	}

	numerator(x:%):R == {
		import from Z;
		(a, n) := numord x;
		n < 0 => a;
		ASSERT(n >= 0);
		a * p^n;
	}

	denominator(x:%):R == {
		import from Z;
		(a, n) := numord x;
		n < 0 => p^(-n);
		1;
	}

	-- returns (c, k) s.t. b divides a q^k,
	-- returns k = -1 if there are no such nonnegative k
	-- if q and b are coprime (in particular whenever q is irreducible),
	-- this is equivalent to b divides a
	-- over a gcd domain if q and b are not coprime, this is
	-- equivalent to b/g divides a g^k for some k >= 0 where g = gcd(b, q)
	local powexquo(b:R, a:R, q:R, irrq?:Boolean):(R, Z) == {
		import from Partial R;
		gcd? => gcdpowexquo(b, a, q, irrq?);
		~failed?(u := exactQuotient(a, b)) => (retract u, 0);
		irrq? => (0, -1);
		-- TEMPORARY HACK: tries only whether b divides a p
		~failed?(u := exactQuotient(b, a * p)) => (retract u, 1);
		-- TEMPORARY: THIS IS FALSE!
		(0, -1);
	}

	-- b p^m divides a p^n if and only if b divides a p^k for some k >= 0
	exactQuotient(x:%, y:%):Partial % == {
		TRACE("quotientby::exactQuotient, p = ", p);
		import from Partial R;
		(a, n) := numord x;
		TRACE("a = ", a); TRACE("n = ", n);
		(b, m) := numord y;
		TRACE("b = ", b); TRACE("m = ", m);
		e := n - m;
		TRACE("e = ", e);
		(c, k) := powexquo(b, a, p, irr?);
		k < 0 => {
			gcd? => failed;
			-- TEMPORARY HACK: tries whether b divides a p^|e|
			(ee := abs e) > 2 and
				~failed?(u := exactQuotient(a * p^ee, b)) => {
					e > 0 => [retract(u)::%];
					(c, q) := numord(retract(u)::%);
					[mkquot(c, e + e + q)];
			}
			error "QuotientBy::exactQuotient - cannot conclude"
		}
		[mkquot(c, e - k)];
	}

	if R has GcdDomain then {
		normalize(x:%):% == x;

		local gcdpowexquo(b:R, a:R, q:R, irrq?:Boolean):(R, Z) == {
			import from Partial R;
			~failed?(u := exactQuotient(a, b)) => (retract u, 0);
			irrq? => (0, -1);
			(g, bb, qq) := gcdquo(b, q)$R;	-- TEMPO: 1.1.11e BUG
			unit? g => (0, -1);
			(h, k) := powexquo(bb, a, g, false);
			k < 0 => (0, -1);
			(h * qq^(next k), next k);
		}
	}

	shift(x:%, n:Z):% == {
		(a, m) := numord x;
		zero? a or zero? n => x;
		mkquot(a, n + m);
	}

	-(x:%):% == {
		(a, n) := numord x;
		zero? a => 0;
		mkquot(- a, n);
	}

	(x:%)^(n:Z):% == {
		zero? x or one? x or zero? n => 1;
		one? n => x;
		ASSERT(n > 1);
		(a, m) := numord x;
		mkquot(a^n, n * m);
	}

	(x:%) = (y:%):Boolean == {
		(a, n) := numord x;
		(b, m) := numord y;
		n = m and a = b;
	}

	(x:%) * (y:%):% == {
		zero? x or zero? y => 0;
		(a, n) := numord x;
		(b, m) := numord y;
		irr? => mkquot(a * b, n + m);
		(c, q) := numord((a * b)::%);
		mkquot(c, n + m + q);
	}

	(c:R) * (x:%):% == {
		zero? c or zero? x => 0;
		one? c => x;
		(a, n) := numord x;
		irr? => {
			(b, m) := numord canon(c, n);
			mkquot(a * b, m);
		}
		canon(c * a, n);
	}

	(x:%) - (y:%):% == {
		zero? x => - y; zero? y => x;
		addsub(x, y, false);
	}

	(x:%) + (y:%):% == {
		zero? x => y; zero? y => x;
		addsub(x, y, true);
	}

	local addsub(x:%, y:%, add?:Boolean):% == {
		(a, n) := numord x;
		(b, m) := numord y;
		n < m => {
			bp := b * p^(m-n);
			s := { add? => a + bp; a - bp; }
			mkquot(s, n);
		}
		n > m => {
			ap := a * p^(n-m);
			s := { add? => ap + b; ap - b; }
			mkquot(s, m);
		}
		s := { add? => a + b; a - b; }
		canon(s, n);
	}

	local canon(a:R, n:Z):% == {
		TRACE("QuotientBy::canon: ", a);
		TRACE("p^", n);
		zero? a => 0;
		(m, a) := orderpquo a;
		TRACE("QuotientBy::canon: returning ", a);
		TRACE("p^", n + m);
		mkquot(a, n + m);
	}

	local liftPconstant(D:Derivation R):Derivation(% pretend Ring) == {
		derivation {(f:%):% +-> {
			(a, n) := numord f;
			canon(D a, n);
		}}
	}

	lift(D:Derivation R):Derivation(% pretend Ring) == {
		zero?(dp := D p) => liftPconstant D;
		-- p'/p = dppa p^dppn
		(dppa, dppn) := numord canon(dp, -1);
		derivation {(f:%):% +-> {
			(a, n) := numord f;
			da := D a;
			zero? n => da::%;
			ASSERT(~zero? dppa);
			local b:R; local m:Z;
			-- compute b,m s.t. a p'/p = b p^m,  p \nodiv b
			if irr? then {
				b := a * dppa;
				m := dppn;
			}
			else (b, m) := numord canon(a * dppa, dppn);
			m >= 0 => canon(da + n * b * p^m, n);
			mkquot(da * p^(-m) + n * b, n + m);
		} }
	}

	if R has OrderedRing then {
		(x:%) > (y:%):Boolean == {
			(a, n) := numord x;
			(b, m) := numord y;
			n > m or (n = m and a >$R b);	-- TEMPO: 1.1.11e BUG
		}
	}

	if R has FiniteCharacteristic then {
		pthPower(x:%):% == {
			(a, n) := numord x;
			ap := pthPower(a)$R;	-- TEMPO: 1.1.11e BUG
			np := characteristic$R * n;
			irr? => mkquot(ap, np);
			canon(ap, np);
		}
	}
	}		
}
