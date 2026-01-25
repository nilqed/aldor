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
----------------------------- mgcd.as ----------------------------------
#include "sumit"

MultiGcd(R:GcdDomain, P:UnivariatePolynomialCategory0 R): with {
	multiGcd: List P -> (P, List P);
} == add {

	macro { MODULUS == 65535; HALFMODULUS == 32767; };

	-- Takes a random linear combination to minimize the
	-- number of gcd's
	-- (Zippel, "Effective Polynomial Computation", p.127)
	multiGcd(l:List P):(P, List P) == {
		TRACE("gcd of list ", l);
		import from R, Partial P, List Partial P;
		import from Integer, RandomNumberGenerator;
		empty? l => (1, l);
		a := first l;		-- l.1
		empty?(r := rest l) => (a, [1]);
		b := first r;		-- l.2
		empty?(r := rest r) => {
			(g, y, z) := gcdquo(a, b);
			(g, [y, z]);
		}
		b := copy b;
		-- compute b = l.2 + c3 l.3 + c4 l.4 + ...
		while ~empty? r repeat {
			-- keep the random coefficients "small" and balanced
			-- don't use random()$R since integers are wanted
			c := (randomInteger() rem MODULUS) - HALFMODULUS;
			if zero? c then c := HALFMODULUS;
			b := add!(b, c::R, first r);
			r := rest r;
		}
		TRACE("gcd:computing gcd of = ", a); TRACE("and ", b);
		g := gcd(a, b);
		TRACE("gcd:candidate gcd = ", g);
		-- g is probably gcd(a, l), could be a multiple
		(quotients, bad) := exquo(l, g);
		empty? bad => (g, [retract q for q in quotients]);
		-- g is not the true gcd, but a multiple of it
		(newg, quots) := multiGcd cons(g, bad);
		(newg, merge(quotients, quots));
	}

	local exquo(l:List P, g:P):(List Partial P, List P) == {
		import from Partial P;
		q:List Partial P := empty();
		bad:List P := empty();
		for x in l repeat {
			q := cons(u := exactQuotient(x, g), q);
			if failed? u then bad := cons(x, bad);
		}
		(reverse! q, reverse! bad);
	}

	-- first(lq) is the correction factor to multiply the quotients in lquot
	-- rest(lq) contains the "missing" quotients in lquot
	local merge(lquot:List Partial P, lq:List P):List P == {
		l:List P := empty();
		ASSERT(~empty? lq);
		c := first lq; lq := rest lq;
		for q in lquot repeat {
			if failed? q then {
				l := cons(first lq, l); lq := rest lq;
			}
			else l := cons(c * retract q, l);
		}
		reverse! l;
	}
}
