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
------------------------ nnquotby.as ---------------------------
#include "sumit"

macro {
	Z == Integer;
	PR == SparseUnivariatePolynomial R;
}

#if ASDOC
\thistype{NonNormalizingQuotientBy}
\History{Manuel Bronstein}{7/6/96}{created}
\Usage{import from \this(R, p)}
\Params{
{\em R} & IntegralDomain & an integral domain\\
{\em p} & R & a nonzero nonunit of R\\
}
\Descr{
\this(R, p) forms the quotient of the integral domain {\em R} by the
nonzero nonunit {\em p}, \ie the set of all fractions whose denominator is a
power of {\em p}.
}
\begin{exports}
\category{QuotientByCategory R}\\
\end{exports}
#endif

NonNormalizingQuotientBy(R: IntegralDomain, p:R): QuotientByCategory R == {
	-- sanity checks on the parameters
	ASSERT(~zero? p);
	ASSERT(~unit? p);
	add {
	-- value is Numerator p^Order
	macro Rep == Record(Numerator:R, Order:Z, Normal?:Boolean);
	import from Rep;

	local gcd?:Boolean			== R has GcdDomain;
	local mkquot(a:R, n:Z, n?:Boolean):%	== per [a, n, n?];
	0:%					== mkquot(0, 0, true);
	1:%					== mkquot(1, 0, true);
	coerce(a:R):%				== mkquot(a, 0, false);
	local numord(x:%):(R, Z, Boolean)	== explode rep x;
	local orderpquo:R -> (Z, R)		== orderquo p;
	order(x:%):Z			== { x := normalize! x; rep(x).Order; }

	random():% == {
		import from Z, R, RandomNumberGenerator;
		mkquot(random(), (randomInteger() rem 101) - 50, false);
	}

	zero?(x:%):Boolean == {
		(a, n, n?) := numord x;
		zero? a;
	}

	one?(x:%):Boolean == {
		(a, n, n?) := numord x;
		n? => one? a and zero? n;
		n > 0 => false;
		(a, n, n?) := numord normalize! x;
		one? a and zero? n;
	}
		
	numerator(x:%):R == {
		import from Z;
		(a, n, n?) := numord x;
		n >= 0 => a * p^n;
		(a, n, n?) := numord normalize! x;
		n >= 0 => a * p^n;
		a;
	}

	denominator(x:%):R == {
		import from Z;
		(a, n, n?) := numord x;
		n >= 0 => 1;
		(a, n, n?) := numord normalize! x;
		n >= 0 => 1;
		p^(-n);
	}

	-- returns (c, k) s.t. b divides a q^k,
	-- returns k = -1 if there are no such nonnegative k
	-- if q and b are coprime (in particular whenever q is irreducible),
	-- this is equivalent to b divides a
	-- over a gcd domain if q and b are not coprime, this is
	-- equivalent to b/g divides a g^k for some k >= 0 where g = gcd(b, q)
	local powexquo(b:R, a:R, q:R):(R, Z) == {
		import from Partial R;
		gcd? => gcdpowexquo(b, a, q);
		~failed?(u := exactQuotient(a, b)) => (retract u, 0);
		-- TEMPORARY HACK: tries only whether b divides a p
		~failed?(u := exactQuotient(b, a * p)) => (retract u, 1);
		-- TEMPORARY: THIS IS FALSE!
		(0, -1);
	}

	-- b p^m divides a p^n if and only if b divides a p^k for some k >= 0
	exactQuotient(x:%, y:%):Partial % == {
		import from Partial R;
		(a, n, n?) := numord normalize! x;
		(b, m, n?) := numord normalize! y;
		e := n - m;
		(c, k) := powexquo(b, a, p);
		k < 0 => {
			gcd? => failed;
			-- TEMPORARY HACK: tries whether b divides a p^|e|
			(ee := abs e) > 2 and
				~failed?(u := exactQuotient(a * p^ee, b)) => {
					e > 0 => [retract(u)::%];
					[mkquot(retract u, e + e, false)];
			}
			error "QuotientBy::exactQuotient - cannot conclude"
		}
		[mkquot(c, e - k, false)];
	}

	if R has GcdDomain then {
		normalize(x:%):% == normalize! mkquot numord x;

		local gcdpowexquo(b:R, a:R, q:R):(R, Z) == {
			import from Partial R;
			~failed?(u := exactQuotient(a, b)) => (retract u, 0);
			(g, bb, qq) := gcdquo(b, q)$R;	-- TEMPO: 1.1.11e BUG
			unit? g => (0, -1);
			(h, k) := powexquo(bb, a, g);
			k < 0 => (0, -1);
			(h * qq^(next k), next k);
		}
	}

	shift(x:%, n:Z):% == {
		(a, m, n?) := numord x;
		zero? a or zero? n => x;
		mkquot(a, n + m, n?);
	}

	-(x:%):% == {
		(a, n, n?) := numord x;
		zero? a => 0;
		mkquot(- a, n, n?);
	}

	(x:%)^(n:Z):% == {
		zero? x or one? x or zero? n => 1;
		one? n => x;
		(a, m, n?) := numord x;
		mkquot(a^n, n * m, false);
	}

	(x:%) = (y:%):Boolean == {
		(a, n, n?) := numord normalize! x;
		(b, m, n?) := numord normalize! y;
		n = m and a = b;
	}

	(x:%) * (y:%):% == {
		zero? x or zero? y => 0;
		(a, n, n?) := numord x;
		(b, m, n?) := numord y;
		mkquot(a * b, n + m, false);
	}

	(c:R) * (x:%):% == {
		zero? c or zero? x => 0;
		one? c => x;
		(a, n, n?) := numord x;
		mkquot(c * a, n, false);
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
		(a, n, a?) := numord x;
		(b, m, b?) := numord y;
		n < m => {
			bp := b * p^(m-n);
			s := { add? => a + bp; a - bp; }
			mkquot(s, n, a? and b?);
		}
		n > m => {
			ap := a * p^(n-m);
			s := { add? => ap + b; ap - b; }
			mkquot(s, m, a? and b?);
		}
		s := { add? => a + b; a - b; }
		mkquot(s, n, false);
	}

	local normalize!(x:%):% == {
		(a, n, n?) := numord x;
		TRACE("QuotientBy::normalize!: ", a);
		TRACE("p^", n);
		n? => x;
		rep(x).Normal? := true;
		zero? a => {
			rep(x).Order := 0;
			x;
		}
		(m, a) := orderpquo a;
		TRACE("QuotientBy::normalize!: returning ", a);
		TRACE("p^", n + m);
		rep(x).Numerator := a;
		rep(x).Order := n + m;
		x;
	}

	local liftPconstant(D:Derivation R):Derivation(% pretend Ring) == {
		derivation {(f:%):% +-> {
			(a, n, n?) := numord f;
			mkquot(D a, n, false);
		}}
	}

	lift(D:Derivation R):Derivation(% pretend Ring) == {
		zero?(dp := D p) => liftPconstant D;
		derivation {(f:%):% +-> {
			(a, n, n?) := numord f;
			da := D a;
			zero? n => da::%;
			ASSERT(~zero? dp);
			mkquot(da * p + n * a * dp, n - 1, false);
		} }
	}

	if R has OrderedRing then {
		(x:%) > (y:%):Boolean == {
			(a, n, n?) := numord normalize! x;
			(b, m, n?) := numord normalize! y;
			n > m or (n = m and a >$R b);	-- TEMPO: 1.1.11e BUG
		}
	}

	if R has FiniteCharacteristic then {
		pthPower(x:%):% ==  {
			(a, n, n?) := numord x;
			-- TEMPO: 1.1.11e INFERENCE BUG
			mkquot(pthPower(a)$R, characteristic$R * n, false);
		}
	}
	}		
}
