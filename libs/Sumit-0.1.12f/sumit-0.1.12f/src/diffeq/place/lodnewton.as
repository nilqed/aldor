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
--------------------------- lodnewton.as ----------------------------
#include "sumit"

#if ASDOC
\thistype{LinearOrdinaryDifferentialNewtonPolygon}
\History{Manuel Bronstein}{24/5/95}{created}
\History{Manuel Bronstein}{21/1/98}{added characteristic equation}
\Usage{import from \this(C, R, P, L)}
\Params{
{\em C} & CommutativeRing & the coefficients of the operator\\
{\em R} & CommutativeRing & the residue ring at the place\\
{\em P} & DifferentialPlace(C, R) & a place where to localize\\
{\em L} & LinearOrdinaryDifferentialOperatorCategory C & operators\\
}
\Descr{\this(C, R, P, L) provides local analysis tools for linear ordinary
differential operators at the place P.}
\begin{exports}
characteristicEquation: & (\%, Z) $\to$ Rx &
characteristic equation of a slope\\
envelope: & \% $\to$ List Cross(Z, Z) & hull of the Newton polygon\\
indicialEquation: & \% $\to$ UP & indicial equation\\
irregular?: & \% $\to$ Boolean & check for an irregular singularity\\
newtonPolygon: & L $\to$ \% & create a Newton polygon\\
orderDrop: & \% $\to$ Z & the order drop of an operator\\
ordinary?: & \% $\to$ Boolean & check for a singularity\\
regular?: & \% $\to$ Boolean & check for a regular singularity\\
slopes: & \% $\to$ List Quotient Z & slopes on the convex hull\\
\end{exports}
\begin{aswhere}
Z &==& Integer\\
UP &==& GeneralizedPochammerUnivariatePolynomial R\\
Rx &==& SparseUnivariatePolynomial R\\
\end{aswhere}
\begin{exports}[if R has RationalRootRing then]
integerExponents: & \% $\to$ List Integer & integer exponents\\
rationalExponents: & \% $\to$ List RationalRoot & rational exponents\\
\end{exports}
#endif

macro {
	Z	== Integer;
	Q	== Quotient Integer;
	RR	== RationalRoot;
	Rx	== SparseUnivariatePolynomial R;
	POCH	== GeneralizedPochammerMonomial R;
	GPOCH	== GeneralizedPochammerUnivariatePolynomial R;
}

LinearOrdinaryDifferentialNewtonPolygon(C:CommutativeRing,
	R:CommutativeRing, P:DifferentialPlace(C, R),
	L:LinearOrdinaryDifferentialOperatorCategory C): with {
		characteristicEquation:	(%, Z) -> Rx;
#if ASDOC
\aspage{characteristicEquation}
\Usage{\name(p, n)}
\Signature{(\%, Integer)}{SparseUnivariatePolynomial R}
\Params{
{\em p} & \% & a Newton polygon\\
{\em n} & Integer & a slope of p\\
}
\Retval{Returns the characteristic equation for the slope n
of the operator corresponding to the Newton polygon p.}
\seealso{indicialEquation (\this)}
#endif
		envelope:		% -> List Cross(Z, Z);
#if ASDOC
\aspage{envelope}
\Usage{\name~p}
\Signature{\%}{List Cross(Integer, Integer)}
\Params{ {\em p} & \% & a Newton polygon\\ }
\Retval{Returns the list of points which form the lower right convex hull of
the Newton polygon p.}
#endif
		indicialEquation:	% -> GPOCH;
#if ASDOC
\aspage{indicialEquation}
\Usage{\name~p}
\Signature{\%}{DenseUnivariatePolynomial R}
\Params{ {\em p} & \% & a Newton polygon\\ }
\Retval{Returns the indicial equation
of the operator corresponding to the Newton polygon p.}
\seealso{characteristicEquation (\this)}
#endif
		if R has RationalRootRing then integerExponents: % -> List Z;
#if ASDOC
\aspage{integerExponents}
\Usage{\name~p}
\Signature{\%}{List Integer}
\Params{ {\em p} & \% & a Newton polygon\\ }
\Retval{Returns $[r_1,\dots,r_n]$ where the $r_i$'s are
the integer exponents of $p$.}
#endif
		irregular?:		% -> Boolean;
#if ASDOC
\aspage{irregular?}
\Usage{\name~p}
\Signature{\%}{Boolean}
\Params{ {\em p} & \% & a Newton polygon\\ }
\Retval{Returns \true~if P is an irregular singularity
of the operator corresponding to the Newton polygon p, \false~otherwise.}
\seealso{ordinary?(\this),\\ regular?(\this)}
#endif
		newtonPolygon:		L -> %;
#if ASDOC
\aspage{newtonPolygon}
\Usage{\name~l}
\Signature{l}{\%}
\Params{ {\em l} & L & a differential operator\\ }
\Retval{Returns the Newton polygon of l at the place $P$.}
\Remarks{The Newton polygon of l should be created first with this function,
then passed instead of l to all the other functions of this type. This prevents
the polygon calculations from being repeated several times. Note that if P
is a set of affine points, then its center must be balanced with respect to
the coefficients of l. This fact is not checked by this function.}
#endif
		orderDrop:		% -> Z;
#if ASDOC
\aspage{orderDrop}
\Usage{\name~p}
\Signature{\%}{Integer}
\Params{ {\em p} & \% & a Newton polygon\\ }
\Retval{Returns the order drop at P of the operator l corresponding
to the Newton polygon p, \ie the value of $\nu(l f) - \nu(f)$ for any
$f \in C$ when $\nu(f) \ne 0$ and no cancellation occurs.}
#endif
		ordinary?:		% -> Boolean;
#if ASDOC
\aspage{ordinary?}
\Usage{\name~p}
\Signature{\%}{Boolean}
\Params{ {\em p} & \% & a Newton polygon\\ }
\Retval{Returns \true~if P is an ordinary point of the operator
corresponding to the Newton polygon p, \false~if P is a singularity.}
\seealso{irregular?(\this),\\ regular?(\this)}
#endif
		if R has RationalRootRing then rationalExponents: % -> List RR;
#if ASDOC
\aspage{rationalExponents}
\Usage{\name~p}
\Signature{\%}{List RationalRoot}
\Params{ {\em p} & \% & a Newton polygon\\ }
\Retval{Returns $[(r_1,e_1),\dots,(r_n,e_n)]$ where the $r_i$'s are
the rational exponents of $p$ and have multiplicity $e_i$.}
#endif
		regular?:		% -> Boolean;
#if ASDOC
\aspage{regular?}
\Usage{\name~p}
\Signature{\%}{Boolean}
\Params{ {\em p} & \% & a Newton polygon\\ }
\Retval{Returns \true~if P is a regular singularity
of the operator corresponding to the Newton polygon p, \false~otherwise.}
\seealso{irregular?(\this),\\ ordinary?(\this)}
#endif
		slopes:			% -> List Q;
#if ASDOC
\aspage{slopes}
\Usage{\name~p}
\Signature{\%}{List Quotient Integer}
\Params{ {\em p} & \% & a Newton polygon\\ }
\Retval{Returns the list of slopes of the convex hull of the Newton polygon p.}
#endif
} == add {
	macro Rep == Record(op:L, mu:Z, pts: List Cross(Z,Z),
					env: List Cross(Z,Z), eq: GPOCH);

	import from Rep;

	local points(p:%):List Cross(Z, Z)	== rep(p).pts;
	local operator(p:%):L			== rep(p).op;
	orderDrop(p:%):Z			== rep(p).mu;
	local equation(p:%):GPOCH		== rep(p).eq;
	local envlop(p:%):List Cross(Z, Z)	== rep(p).env;
	local ptx(x:Z, y:Z):Z			== x;
	local pty(x:Z, y:Z):Z			== y;
	local singular?(p:%):Boolean		== ~ordinary? p;
	regular?(p:%):Boolean		== { import from Z; classify(p) > 0; }
	irregular?(p:%):Boolean		== { import from Z; classify(p) < 0; }
	ordinary?(p:%):Boolean		== { import from Z; zero? classify p; }
	newtonPolygon(p:L):%		== { ASSERT(~zero? p); computePoints p }

	local slope(x:Z, y:Z, xx:Z, yy:Z):Q == {
		ASSERT(x ~= xx);
		(yy - y) / (xx - x);
	}

	slopes(p:%):List Q == {
		import from List Cross(Z, Z);
		s:List Q := empty();
		l := envelope p;
		ASSERT(~empty? l);
		(x, y) := first l;
		for pt in rest l repeat {
			(xx, yy) := pt;
			s := cons(slope(x, y, xx, yy), s);
		}
		s;
	}

	local prod(n:Z, r:R):Rx == {
		p:Rx := 1;
		for i in 0..prev n repeat p := times!(p, monom - (i*r)::Rx);
		p;
	}

	characteristicEquation(p:%, s:Z):Rx == {
		import from List Z, R, P, L;
		ASSERT(s >= 0);
		l := points p;
		ASSERT(~empty? l);
		-- the order corresponding to s is -delta, where
		-- delta = s - orderDrop derivation
		-- compute all the points (i,j) maximizing i delta - nu(a_i)
		-- since x = i and y = nu(a_i) + e i, where e = order drop,
		-- we have  i delta - nu(a_i) = x s - y
		(x, y) := first l;
		n := x * s - y;
		xcoords:List Z := [x];
		for pt in rest l repeat {
			(x, y) := pt;
			m := x * s - y;
			if m > n then {
				n := m;
				xcoords := [x];
			}
			else if m = n then xcoords := cons(x, xcoords);
		}
		-- xcoords contains all the points contributing to the equation
		-- the characteristic equation at infinity is useless if s=0
		zs? := zero? s;
		r:R := { zs? => residue derivation; 0 }
		q:Rx := 0;
		op := operator p;
		for i in xcoords repeat {
			phi := leadingCoefficient(coefficient(op, i));
			q := {
				zs? => add!(q, phi * prod(i, r));
				add!(q, phi, i);
			}
		}
		q;
	}

#if ASTRACE
	local trace(p:TextWriter, l:List Cross(Z, Z)):() == {
		for point in l repeat {
			(a, b) := point;
			p << " (" << a << "," << b << ") ";
		}
		p << newline;
	}

	local trace(p:%):() == {
		import from StandardIO, TextWriter, ExpressionTree, L;
		err := writer stderr;
		err << "::POLYGON of " << newline;
		maple(err, extree operator p);
		err << newline;
		err<<"::order drop = "<<orderDrop p<<newline<< "::points = ";
		trace(err, points p);
		err << "::enveloppe = ";
		trace(err, envlop p);
		err << "::indicial equation = " << newline;
		maple(err, extree equation p);
		err << newline << newline;
	}
#endif

	-- return 0 for ordinary, 1 for regular, -1 for irregular
	local classify(p:%):Z == {
		import from List Z, POCH, GPOCH;
		~empty? rest envelope p => -1;
		l := integerRoots(lowestTerm indicialEquation p);
		for n in 0..prev degree operator p repeat
			~member?(n, l) => return 1;
		0;
	}

	indicialEquation(p:%):GPOCH == {
		zero? equation p =>
			rep(p).eq := computeIndicialEquation(orderDrop p,
							operator p, points p);
		equation p;
	}

	if R has RationalRootRing then {
		integerExponents(p:%):List Z == {
			import from RR, List RR;
			l := integerRoots indicialEquation p;
			[integerValue rt for rt in l];
		}

		rationalExponents(p:%):List RR == {
			import from POCH, GPOCH, List Z, Rx;
			eq := indicialEquation p;
			q := expand(normalize eq, Rx);
			merge(rationalRoots q, integerRoots lowestTerm eq, q);
		}

		-- the roots in lt appear degree$P times
		-- the number of appearances of the roots of q in l
		-- must be computed by the place
		local merge(l:List RR, lt:List Z, q:Rx):List RR == {
			import from Z, RR, Partial RR;
			TRACE("lodnewton::merge: lr = ", lr);
			TRACE("lodnewton::merge: lt = ", lt);
			m := degree$P;
			TRACE("lodnewton::merge: place has degree ", m);
			lr:List RR := empty();
			for rt in l repeat {
				(n, d) := value rt;
				e := (multiplicity(rt, Rx)$P)(q);
				if integer? rt then
					e := e +  find(integerValue rt, lt, m);
				lr := cons(rationalRoot(n, d, e), lr);
			}
			for nn in lt | ~member?(nn, l) repeat
				lr := cons(integerRoot(nn, m), lr);
			lr;
		}

		local member?(n:Z, l:List RR):Boolean == {
			import from RR;
			for rt in l | integer? rt repeat {
				n = integerValue rt => return true;
			}
			false;
		}

		-- returns m if n is in l, 0 otherwise
		local find(n:Z, l:List Z, m:Z):Z == {
			for k in l repeat { n = k => return m; }
			0;
		}
	}

	envelope(p:%):List Cross(Z, Z) == {
		empty? envlop p => rep(p).env := computeEnvelope points p;
		envlop p;
	}

	local computePoints(p:L):% == {
		import from Z, Partial Z, P;
		TRACE("computePoints::p = ", p);
		n := degree p;
		epsilon := orderDrop derivation;
		TRACE("epsilon = ", epsilon);
		-- the leading coefficient is known to be <> 0, so order is safe
		yn := drop := orderOf leadingCoefficient p + epsilon * n;
		-- the rightmost point in the polygon has coordinates (n, yn)
		pt:Cross(Z, Z) := (n, yn);
		l:List Cross(Z,Z) := [pt];
		for i in n-1..0 by -1 repeat {
			-- pts with y > yn can be ignored, this corresponds to
			-- orderOf(a_i) > yn - i * epsilon
			u := orderOf(coefficient(p, i), yn - i * epsilon);
			if ~failed? u then {
				m := retract(u) + epsilon * i;
	    			if m < drop then drop := m;
	    			l := cons((i, m), l);
			}
		}
		per [p, drop, l, empty(), 0];
	}

	local computeIndicialEquation(m:Z,p:L,points:List Cross(Z,Z)):GPOCH == {
		import from List Z, R, P, POCH, List POCH;
		r := residue derivation;
		e := orderDrop derivation;
		-- points is sorted in ascending order
		xcoords := [ptx pt for pt in points | m = pty pt];
		ASSERT(~empty? xcoords);
		xmin := first xcoords;
		-- since r ~= 0 at a normal place, we can eliminate the
		-- common content r^xmin from the indicial equation
		-- even if r contains parameters
		-- (otherwise we would have r^n rather than r^(n-xmin)
		polynomial [monomial(leadingCoefficient(coefficient(p, n))
				* r^(n - xmin), 0, n, e) for n in xcoords];
	}

	local computeEnvelope(points:List Cross(Z,Z)):List Cross(Z, Z) ==
		computeEnv(sorty points, points, reverse points);


	local insert!(n:Z, l:List Z):List Z == {
		empty? l or n > first l => cons(n, l);
		n = first l => l;
		cons(first l, insert!(n, rest l));
	}

	local sorty(points:List Cross(Z, Z)):List Z == {
		l:List(Z) := empty();
		for pt in points repeat { (x, y) := pt; l := insert!(y, l); }
		l;
	}

	local computeEnv(ly:List Z, points:List Cross(Z, Z),
		rpoints:List Cross(Z,Z)):List Cross(Z, Z) == {
			empty? ly or empty? points => empty();
			m := first ly;
			scan := rpoints;
			while pty first scan > m repeat scan := rest scan;
			(x0, y0) := first scan;	-- righmost point with y = m
			while ptx first scan ~= x0 repeat points := rest points;
			cons((x0,y0), computeEnv(rest ly,rest points,rpoints));
	}
}


#if SUMITTEST
---------------------- test lodnewton.as --------------------------
#include "sumittest"

macro {
	Z  == Integer;
	Q  == Quotient Z;
	Qx == DenseUnivariatePolynomial Q;
	Fd == LinearOrdinaryDifferentialOperator Qx;
	X0 == RationalPlace(Q, Qx, 0);
	NP == LinearOrdinaryDifferentialNewtonPolygon(Qx, Q, X0, Fd);
	GPOCH	== GeneralizedPochammerUnivariatePolynomial Q;
}

euler():Boolean == {
	import from Z, Q, Qx, Fd, X0, NP, GPOCH;
	x:Qx := monom;
	dx:Fd := monom;
	euler := x^3 * dx^2 + (x^2 + x) * dx - 1;
	-- euler has an irregular singularity with exponent 1 at x = 0
	np := newtonPolygon euler;
	ieq := expand(indicialEquation np, Qx);
	zero?(ieq(1@Q)) and degree(ieq) = 1 and irregular? np;
}

legendre():Boolean == {
	import from Z, Q, Qx, Fd, X0, NP, GPOCH;
	x:Qx := monom;
	dx:Fd := monom;
	legendre := (1 - x^2) * dx^2 - 2 * x * dx + 30::Fd;
	np := newtonPolygon legendre;
	ieq := expand(indicialEquation np, Qx);
	zero?(ieq(1@Q)) and zero?(ieq(0@Q)) and degree(ieq)=2 and ordinary? np;
}

print << "Testing lodnewton..." << newline;
sumitTest("euler", euler);
sumitTest("legendre", legendre);
print << newline;
#endif

