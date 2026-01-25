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
------------------------- balfact.as --------------------------
#include "sumit"

macro Z	== Integer;

BalancedFactorization(R:GcdDomain, P:UnivariatePolynomialCategory R): with {
	balancedFactor: (P, List P) -> Product P;
	if R has RationalRootRing then
		refineInteger: Product P -> Product P;
} == add {
	balancedFactor(a:P, l:List P):Product P == {
		TRACE("balancedFactor ", a);
		TRACE("w.r.t. ", l);
		(c, sa) := squareFree a;
		TRACE("squarefree factorisation = ", sa);
		p:Product P := 1;
		for t in sa repeat {
			(b, n) := t;
			p := p * balancedFactor(b, n, l);
		}
		TRACE("balanced factorisation = ", p);
		p;
	}

	local balancedFactor(a:P, n:Z, l:List P):Product P == {
		b := first l;
		empty? rest l => balancedFactor(a, n, b);
		p:Product P := 1;
		for t in balancedFactor(a, n, rest l) repeat {
			(c, m) := t;
			p := p * balancedFactor(c, n, b);
		}
		p;
	}

	local balancedFactor(a:P, n:Z, b:P):Product P == {
		TRACE("balancedFactor, a = ", a);
		TRACE("b = ", b);
		(g, a, dummy) := gcdquo(a, b);
		p := term(a, n);
		zero? degree g => p;
		(m, q) := orderquo(g)(b);
		ASSERT(m > 0);
		p * balancedFactor(g, n, q);
	}

	if R has RationalRootRing then {
		refineInteger(p:Product P):Product P == {
			q:Product P := 1;
			for t in p repeat q := q * refineInteger t;
			q;
		}

		local refineInteger(p:P, n:Z):Product P == {
			import from RationalRoot, List RationalRoot;
			q:Product P := 1;
			x:P := monom;
			for rt in integerRoots p repeat {
				l := x - integerValue(rt)::P;
				m := multiplicity rt;
				q := times!(q, l, n + m);
				p := quotient(p, l^m);
			}
			times!(q, p, n);
		}
	}
}
