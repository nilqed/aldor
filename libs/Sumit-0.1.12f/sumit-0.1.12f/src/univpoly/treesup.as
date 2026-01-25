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
----------------------------- treesup.as ----------------------------------
#include "sumit.as"

macro Z == Integer

#library Symlib  "symbol.aso"
#library Umonom  "umonom.aso"
#library Upolyc  "upolycat.aso"
#library Tree	 "bintree.aso"
#library AVLTree "avltree.aso"

import from {Symlib, Umonom, Upolyc, Tree, AVLTree};

TreeSUP(F:Ring): UPolyCat F with {
	apply: (OutPort, %, Symbol) -> OutPort;
} == add {
	macro Term	== UnivariateMonomial F;
	macro Rep	== AVLTree Term;  -- sorted smallest term left
	import from {Term, Rep, F, Z};

	0:%				== per empty();
	1:%				== per tree monomial(1, 0);
	sample:%			== monomial(1, 1);
	degree(p:%):Z			== {zero? p => 0;degree rightMost rep p}
	coerce(c:F):%			== per tree monomial(c, 0);
	(x:%) = (y:%):Boolean		== rep x = rep y;
	apply(p:OutPort, x:%):OutPort	== p(x, anonymousVariable());
	leadingCoefficient(p:%):F== {zero? p => 0; coefficient rightMost rep p}
	leadingMonomial(p:%):%		== per tree rightMost rep p;
	minusTerm(t:Term):Term		== monomial(- coefficient t, degree t);
	copyTerm(t:Term):Term		== monomial(coefficient t, degree t);
	-(p:%):%			== per apply(minusTerm, rep p);

	-- can do better here
	reductum(p:%):% == {
		zero? p => 0;
		p - leadingMonomial p;
	}

	monomial(c:F, n:Z):% == {
		ASSERT(n >= 0);
		zero? c => 0;
		per tree monomial(c, n);
	}

	coefficient(p:%, n:Z):F == {
		ASSERT(n >= 0);
		import from Partial Term;
		failed?(t := search(monomial(1, n), rep p)) => 0;
		coefficient retract t;
	}

	apply(p:OutPort, x:%, v:Symbol):OutPort == {
		import from List Term;
		empty?(l := reverse! inOrder rep x) => p(0$F);
		while l repeat {
			p := p(first l, v);
			if (l := rest l) then p := p("+");
		}
		p;
	}

	-- really want integral domain here instead
	if F has GcdDomain then {
		(c:F) * (p:%):% == { zero? c => 0; per apply(cterm c, rep p); }

		times!(p:%, c:F):% == {
			zero? c => 0;
			per apply!(cterm! c, rep p);
		}

		times(p:%, c:F, n:Z):% == {
			zero? n => c * p;
			per apply(cterm(c, n), rep p);
		}

		cterm(c:F):(Term->Term) ==
			(t:Term):Term +-> monomial(c * coefficient t, degree t);

		cterm(c:F, n:Z):(Term->Term) ==
			(t:Term):Term +-> monomial(c*coefficient t, n+degree t);

		cterm!(c:F):(Term->Term) ==
			(t:Term):Term +->
				{ setCoefficient!(t, c * coefficient t); t }

		-- z := z + x * c x^n, x and c are nonzero
		addTimes!(z:Rep, x:Rep, c:F, n:Z):Rep == {
			m := root x;
			trm:Term := monomial(c * coefficient m, n + degree m);
			insert!(trm, addCoef trm, z);
			if (t := left x) then z := addTimes!(z, t, c, n);
			if (t := right x) then z := addTimes!(z, t, c, n);
			z;
		}
	}

	add!(x:%, y:%):% == {
		empty?(ty := rep y) => x;
		zero? x => per copy rep y;
		t := root ty;
		insert!(t, addCoef t, tx := rep x);
		if (t0 := left ty) then tx := rep add!(per tx, per t0);
		if (t0 := right ty) then tx := rep add!(per tx, per t0);
		per tx;
	}

	(x:%) + (y:%):% == {
		zero? x => y; zero? y => x;
		add!(per apply(copyTerm, rep x), y);
	}

	(x:%) * (y:%):% == {
		zero? x or zero? y => 0;
		m := root(ty := rep y);
		z := rep times(x, coefficient m, degree m);
		if (t0 := left ty) then z := addTimes!(z, rep x, t0);
		if (t0 := right ty) then z := addTimes!(z, rep x, t0);
		per z;
	}

	-- z := z + x * y, x and y are nonzero
	addTimes!(z:Rep, x:Rep, y:Rep):Rep == {
		m := root y;
		z := addTimes!(z, x, coefficient m, degree m);
		if (t := left y) then z := addTimes!(z, x, t);
		if (t := right y) then z := addTimes!(z, x, t);
		z;
	}

	addCoef(t:Term):(Term -> Term) ==
		(x:Term):Term +->
			{ setCoefficient!(x, coefficient t + coefficient x); x};
}
