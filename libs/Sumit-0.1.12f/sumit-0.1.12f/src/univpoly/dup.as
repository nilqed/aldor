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
----------------------------- dup.as ----------------------------------
#include "sumit"

macro {
	I == SingleInteger;
	Z == Integer;
	Symbol == String;
	anon == "\Box";
}

#if ASDOC
\thistype{DenseUnivariatePolynomial}
\History{Manuel Bronstein}{5/8/94}{created}
\History{Thom Mulders}{27/5/97}{added partial add!}
\Usage{ import from \this~R\\ import from \this(R, x) }
\Params{
{\em R} & SumitRing & The coefficient ring of the polynomials\\
{\em x} & String & The variable name (optional)\\
}
\Descr{\this(R, x) implements dense univariate polynomials with coefficients
in R.}
\begin{exports}
\category{UnivariatePolynomialCategory R}\\
\end{exports}
#endif

DenseUnivariatePolynomial(R:SumitRing, avar:Symbol == anon):
	UnivariatePolynomialCategory R with {
		copy!: (%, I, PrimitiveArray R) -> %;
		-- TEMPORARY: EXPORTED FOR THE PURPOSE OF TUNING THE
		-- KARATSUBA CUTOFFs FOR VARIOUS COEFF RINGS
		-- if R has CommutativeRing then
			-- karatsuba: (%, %, I) -> %;	-- last arg is cutoff
} == add {
	macro Coeffs	== PrimitiveArray R;     -- sorted, lowest first
	-- the size indicates the allocated size of the array, we always
	-- have (deg + 1) <= siz but not necessarily equality
	-- siz is used to determine when to resize the array
	macro Rep	== Record(siz:I, deg:I, koeffs:Coeffs);

	import from Coeffs, Rep, R, I;

	0:%				== { import from Z; monomial(0, 0); }
	1:%				== { import from Z; monomial(1, 0); }
	local intdom?:Boolean		== R has IntegralDomain;
	local size(p:%):I		== rep(p).siz;
	local degr(p:%):I		== rep(p).deg;
	local coeffs(p:%):Coeffs	== rep(p).koeffs;
	degree(p:%):Z			== { zero? p => -1; degr(p)::Z; }
	local setDegree!(p:%, n:I):I	== { ASSERT(n >= 0); rep(p).deg := n; }
	-- TEMPORARY: CAUSES SEG FAULT IF DECLARED LOCAL! (BUGxxxx)
	-- local new1(n:I):Coeffs		== new next n;
	new1(n:I):Coeffs		== new next n;
	local charTimes(n:I):I		== (characteristic$% * n::Integer)::I;
	extree(p:%):ExpressionTree	== p extreeSymbol avar;
	(p:%) + (q:%):%			== addsub(p, q, true);
	(p:%) - (q:%):%			== addsub(p, q, false);
	local zero?(c:Coeffs, d:I):Boolean	== zero? d and zero?(c.1);
	leadingCoefficient(p:%):R == { zero? p => 0; coefficient(p, degree p); }
	(port:TextWriter) << (p:%):TextWriter   == port(p, avar);
	-- TEMPORARY: EXPORT NOT FOUND IF DEFAULTED FROM ufalg.as
	monom:%	== { import from Z; monomial(1, 1); }

	local kara?:Boolean ==
		R has CommutativeRing and
			(karatsubaCutoff$(R pretend CommutativeRing) > 0);

	local fft?:Boolean ==
		R has FFTRing and (fftCutoff$(R pretend FFTRing) > 0);

	(p:%) * (q:%):% == {
		import from R;
		zero? p or zero? q => 0;
		one? p => q; one? q => p;
		fft? => fftProduct(p, q);
		kara? => kara(p, q);
		naiveProduct(p, q);
	}

	if R has CommutativeRing then {
		macro RR		== R pretend CommutativeRing;
		local karaCutoff:I	== karatsubaCutoff$R;
		local nokara?:Boolean	== zero? karaCutoff;
		local kara(p:%, q:%):%	== karatsuba(p, q, karaCutoff);

		if R has FFTRing then {
			local fftCut:I				== fftCutoff$R;
			local fftprod:(%, %) -> Partial %	== fft(%)$R;

			local fftProduct(p:%, q:%):% == {
				ASSERT(fftCut > 0);
				import from Partial %;
				min(degr p, degr q) < fftCut or
					failed?(u := fftprod(p, q)) => {
						nokara? => naiveProduct(p, q);
						karatsuba(p, q, karaCutoff);
				}
				retract u;
			}
		}


		karatsuba(p:%, q:%, cut:I):% == {
			import from UnivariatePolynomialKaratsuba(RR);
			ASSERT(~zero? p); ASSERT(~zero? q);
			ASSERT(~one? p); ASSERT(~one? q);
			ASSERT(cut > 0);
			dp := degr p;
			dq := degr q;
			result:Coeffs := new(next(d := dp + dq), 0);
			cp := coeffs p;
			cq := coeffs q;
			m := max(dp, dq);
			if m < cut then times!(result, cp, dp, cq, dq);
			else karatsuba!(result, cp, dp, cq, dq, cut, times!);
			dg := { intdom? => d; computeDegree(d, result); }
			per [next d, dg, result];
		}


		local times1(a:%, b:%, l:Z, h:Z):% == {
			import from I, R;
			zero? a => 0;
			zero? b => 0;
			da := degr a;
			db := degr b;
			H := min(da + db, h::I);
			L := l::I;
			H < L => 0;
			Ca := coeffs a;
			Cb := coeffs b;
			r:Coeffs := new(next(H - L), 0);
			for i in 1..next min(da, H) repeat {
				if ~zero?(ca := Ca.i) then {
					k := max(1, i - L);
					for j in max(1, next next(L - i))..min(next db, next next(H - i)) repeat {
						if ~zero?(cb := Cb.j) then
							r.k := r.k + ca * cb;
						k := next k;
					}
				}
			}
			d := computeDegree(H - L, r);
			per [next(H - L), d, r];
		}

		-- computes the low-part of pp / q, destroying p, but not q.
		-- pp is considered to have degree d
		-- p is considered to be low-part of a polynomial pp which is
		-- divisible by q.
		-- trailingDegree(q) 0-coefficients of pp are not included in p.
		local quotlow!(p:%, q:%, d:Z):% == {
			import from RR;
			zero? p => 0;
			(tcoeff, tdeg) := trailingMonomial q;
			div := divideBy tcoeff;
			zero?(degree q - tdeg) => {
				r:% := 0;
				for term in p repeat {
					(a, n) := term;
					r := add!(r, div a, n);
				}
				r;
			}
			dr1 := next d;
			r:% := monomial(1, dr1);
			(a, n) := trailingMonomial p;
			while ~zero?(a) repeat {
				c := div a;
				r := add!(r, c, n);
				-- third parameter of add! can be negative!
				p := add!(p, -c, n - tdeg, q, n, d);
				(a, n) := trailingMonomial p;
			}
			r - monomial(1, dr1);
		}

		-- p is considered to be the high-part of a polynomial pp which
		-- is divisible by q.
		-- computes the high-part of pp / q, destroying p, but not q.
		local quothigh!(p:%, q:%):% == {
			import from RR;
			zero? p => 0;
			(tcoeff, tdeg) := trailingMonomial q;
			lcoeff := leadingCoefficient q;
			div := divideBy lcoeff;
			one? p => monomial(div 1, 0);
			r:% := 0;
			zero?(degree q - tdeg) => {
				for term in p repeat {
					(a, n) := term;
					r := add!(r, div a, n);
				}
				r;
			}
			dq := degree q;
			dp := degree p;
			while dp >= 0 repeat {
				c := div(leadingCoefficient p);
				r := add!(r, c, dp);
				-- third parameter of add! can be negative!
				h := dp - dq;
				p := add!(p, -c, h, q, max(0, tdeg + h), dp);
				dp := degree p;
			}
			r;
		}

		-- lp, hp, lq, hq and s arbitrary
		local smalltimes(p:%, lp:Z, hp:Z, q:%, lq:Z, hq:Z, s:Z):% == {
			zero? p => 0;
			zero? q => 0;
			s < 0 => 0;
			Hp1 := next min(degr p, hp::I);
			Hq1 := next min(degr q, hq::I);
			lpi := max(lp::I, 0);
			lp1 := next lpi;
			lq1 := next max(lq::I, 0);
			Hp1 < lp1 => 0;
			Hq1 < lq1 => 0;
			Cp := coeffs p;
			Cq := coeffs q;
			si := s::I;
			s1 := next si;
			c:Coeffs := new(s1, 0);
			for i in lp1..min(Hp1, lp1 + si) repeat {
				if ~zero?(cp := Cp.i) then {
					k := i - lpi;
					for j in lq1..min(Hq1, lq1 + s1 - k) repeat {
						if ~zero?(cq := Cq.j) then
							c.k := c.k + cp * cq;
						k := next k;
					}
				}
			}
			d := computeDegree(si, c);
			per [s1, d, c]
		}

		-- dir in {-1, 1}, l = max(0, L).
		-- returns p_l+p_(l+1)*x+...+p_h*x^(h-l) if dir = 1 and
		-- p_h+p_(h-1)*x+...+p_l*x*(h-l) if dir = -1.
		local subpoly(p:%, L:Z, h:Z, dir:Z):% == {
			zero? p => 0;
			l := max(0, L);
			if one? dir then {
				h1 := next min(h::I, degr p);
				l1 := next l::I;
				h1 < l1 => return 0;
				d := h1 - l1;
				d1 := next d;
				c:Coeffs := new d1;
				cp := coeffs p;
				k := l1;
				for i in 1..d1 repeat {
					c.i := cp.k;
					k := next k;
				}
			}
			else {
				dp := degr p;
				newh := min(h::I, dp);
				h1 := next newh;
				l1 := next l::I;
				h1 < l1 => return 0;
				d := (h - l)::I;
				d1 := next d;
				c:Coeffs := new(d1, 0);
				cp := coeffs p;
				k := h1;
				for i in next(h::I - newh)..d1 repeat {
					c.i := cp.k;
					k := prev k;
				}
			}
			deg := computeDegree(d, c);
			per [d1, deg, c];
		}

		local lowPart!(p:%, newdeg:Z):% == {
			olddeg := degr p;
			n := newdeg::I;
			d := {
				olddeg > n => {
					c := coeffs p;
					zero? c next n => computeDegree(n, c);
					n;
				}
				olddeg;
			}
			setDegree!(p, d);
			p;
		}

		times(p:%, q:%, s:Z):% == {
			zero? p => 0;
			zero? q => 0;
			dp := degree p;
			dq := degree q;
			h := min(dp + dq, s);
			zero? dq => smalltimes(p, 0, h, q, 0, 0, h); 
			u := (10 * (h - dq)) quo dq;
			u >= 30 => lowPart!(p * q, h);
			u < 3 => lowPart!(halftimes(p, 0, h, q, 0, h, h), h);
			e := 10 - u;
			if u >= 13 then
				e := 20 - u;
			m := h - dq + ((e * dq) quo 10);
			m1 := next m;
			r := copy q;
			r := subpoly(p, 0, m, 1) * r;
			lowPart!(add!(r, 1, m1, halftimes(p, m1, h, q, 0, h - m1, h - m1), 0, h), h);
		}

		macro {
			KARAPC == 70;
			KARACOEFF == 3;
		}

		-- b:Z == 70;
		-- t:Z == 3 * (karatsubaCutoff$R)::Z;

		-- hp - lp = hq - lq = s
		local halftimes(p:%, lp:Z, hp:Z, q:%, lq:Z, hq:Z, s:Z):% == {
			import from R;
			s < KARACOEFF * (karatsubaCutoff$R)::Z =>
					smalltimes(p, lp, hp, q, lq, hq, s);
			m := (KARAPC * s) quo 100;
			m1 := next m;
			r := subpoly(p, lp, lp + m, 1) * subpoly(q, lq, lq + m, 1);
			r := add!(r, 1, m1, halftimes(p, lp + m1, hp, q, lq, lq + s - m1, s - m1), 0, s);
			add!(r, 1, m1, halftimes(q, lq + m1, hq, p, lp, lp + s - m1, s - m1), 0, s);
		}

	}


	if R has IntegralDomain then {

		local divDiffProdOrdinary(a1:%, a2:%, b1:%, b2:%, q:%):% == {
			import from I, Z, R;
			degnumer := max(degree a1 + degree a2, degree b1 + degree b2);
			degdenom := degree q;
			degres := degnumer - degdenom;
			termshigh := (next degres) quo 2;
			termslow := (next degres) - termshigh;
			(tcoeff, tdeg) := trailingMonomial q;
			highnumer1 := times1(a1, a2, next(degnumer - termshigh), degnumer);
			highnumer2 := times1(b1, b2, next(degnumer - termshigh), degnumer);
			highnumer1 := highnumer1 - highnumer2;
			lownumer1 := times1(a1, a2, tdeg, prev(tdeg + termslow));
			lownumer2 := times1(b1, b2, tdeg, prev(tdeg + termslow));
			lownumer1 := lownumer1 - lownumer2;
			lowres := quotlow!(lownumer1, q, prev termslow);
			highres := quothigh!(highnumer1, q);
			add!(lowres, 1, termslow::Z, highres, 0, degres);
		}

		local shiftright!(a:%, s:I):% == {
			zero? a or zero? s => a;
			c := coeffs a;
			d := degr a;
			for i in 1..(next d - s) repeat
				c.i := c.(i+s);
			setDegree!(a,d - s);
			a;
		}

		local divDiffProdKaratsuba(a1:%, a2:%, b1:%, b2:%, q:%):% == {
			import from Z, R;
			da1 := degree a1;
			da2 := degree a2;
			db1 := degree b1;
			db2 := degree b2;
			degnumer := max(da1 + da2, db1 + db2);
			degdenom := degree q;
			degres := degnumer - degdenom;
			(tcoeff, tdeg) := trailingMonomial q;
			termshigh := (next degres + tdeg) quo 2;
			termslow := (next degres + tdeg) - termshigh;
			if termslow <= tdeg then
				lowb:Z := -1;
			else
				lowb := prev termslow;
			highb := next(degnumer - termshigh);
			(al, ah) := lowHighPart(a1, a2, lowb, highb);
			(bl, bh) := lowHighPart(b1, b2, lowb, highb);
			lownumer := al - bl;
			highnumer := ah - bh;
			lownumer := shiftright!(lownumer, tdeg::I);
			lowres := quotlow!(lownumer, q, prev termslow - tdeg);
			highres := quothigh!(highnumer, q);
			add!(lowres, 1, max(termslow - tdeg,0) , highres, 0, degres);
		}

		

		divDiffProd(a1:%, a2:%, b1:%, b2:%, q:%):% == {
			zero? karaCutoff =>
				divDiffProdOrdinary(a1, a2, b1, b2, q);
			divDiffProdKaratsuba(a1, a2, b1, b2, q);
		}

		local divSumProdOrdinary(a1:%, a2:%, b1:%, b2:%, c1:%, c2:%, q:%):% == {
			import from I, Z, R;
			degnumer := max(degree a1 + degree a2, max(degree b1 + degree b2, degree c1 + degree c2));
			degdenom := degree q;
			degres := degnumer - degdenom;
			termshigh := (next degres) quo 2;
			termslow := (next degres) - termshigh;
			(tcoeff, tdeg) := trailingMonomial q;
			highnumer1 := times1(a1, a2, next(degnumer - termshigh), degnumer);
			highnumer2 := times1(b1, b2, next(degnumer - termshigh), degnumer);
			highnumer3 := times1(c1, c2, next(degnumer - termshigh), degnumer);
			highnumer1 := highnumer1 + highnumer2 + highnumer3;
			lownumer1 := times1(a1, a2, tdeg, prev(tdeg + termslow));
			lownumer2 := times1(b1, b2, tdeg, prev(tdeg + termslow));
			lownumer3 := times1(c1, c2, tdeg, prev(tdeg + termslow));
			lownumer1 := lownumer1 + lownumer2 + lownumer3;
			lowres := quotlow!(lownumer1, q, prev termslow);
			highres := quothigh!(highnumer1, q);
			add!(lowres, 1, termslow::Z, highres, 0, degres);
		}

		local divSumProdKaratsuba(a1:%, a2:%, b1:%, b2:%, c1:%, c2:%, q:%):% == {
			import from Z, R;
			da1 := degree a1;
			da2 := degree a2;
			db1 := degree b1;
			db2 := degree b2;
			dc1 := degree c1;
			dc2 := degree c2;
			degnumer := max(max(da1 + da2, db1 + db2), dc1 + dc2);
			degdenom := degree q;
			degres := degnumer - degdenom;
			(tcoeff, tdeg) := trailingMonomial q;
			termshigh := (next degres + tdeg) quo 2;
			termslow := (next degres + tdeg) - termshigh;
			if termslow <= tdeg then
				lowb:Z := -1;
			else
				lowb := prev termslow;
			highb := next(degnumer - termshigh);
			(al, ah) := lowHighPart(a1, a2, lowb, highb);
			(bl, bh) := lowHighPart(b1, b2, lowb, highb);
			(cl, ch) := lowHighPart(c1, c2, lowb, highb);
			lownumer := al + bl + cl;
			highnumer := ah + bh + ch;
			lownumer := shiftright!(lownumer, tdeg::I);
			lowres := quotlow!(lownumer, q, prev termslow - tdeg);
			highres := quothigh!(highnumer, q);
			add!(lowres, 1, max(termslow - tdeg,0), highres, 0, degres);
		}

		divSumProd(a1:%, a2:%, b1:%, b2:%, c1:%, c2:%, q:%):% == {
			zero? karaCutoff =>
				divSumProdOrdinary(a1, a2, b1, b2, c1, c2, q);
			divSumProdKaratsuba(a1, a2, b1, b2, c1, c2, q);
		}

		local lowHighPart(a:%, b:%, l:Z, h:Z):(%, %) == {
			da := degree a;
			db := degree b;
			if da < db then
				(a, da, b, db) := (b, db, a, da);
			if h > da + db then {
				high:% := 0;
				if l < 0 then
					low:% := 0;
				else
					low := times(a, b, l);
			}
			else
				if l < 0 then {
					low:% := 0;
					d := da + db - h;
					ra := subpoly(a, da - d, da, -1);
					rb := subpoly(b, db - d, db, -1);
					high := times(ra, rb, d);
					high := subpoly(high, 0, d, -1);
				}
				else
					if (h - min(da + db - h, db) <= l) or (l + min(l, db) >= h) then {
						s := a * b;
						low := subpoly(s, 0, l, 1);
						high := subpoly(s, h, da + db, 1);
					}
					else {
						low := times(a, b, l);
						d := da + db - h;
						ra := subpoly(a, da - d, da, -1);
						rb := subpoly(b, db - d, db, -1);
						high := times(ra, rb, d);
						high := subpoly(high, 0, d, -1);
					}
			(low, high);
		}
	}

	trailingMonomial(p:%):(R, Z) == {
		zero? p => (0, -1);
		cp := coeffs p;
		for i in 1..degr p repeat
			~zero?(cp.i) => return(cp.i, prev(i)::Z);
		(cp(next degr p), degree p);
	}

	local newDegree!(p:%, olddeg:I, newdeg:I, c:Coeffs):% == {
		d := {
			olddeg = newdeg => {
				zero? c next newdeg => computeDegree(newdeg, c);
				newdeg;
			}
			max(olddeg, newdeg);
		}
		setDegree!(p, d);
		p;
	}

	add!(p:%, q:%):% == {
		zero? q => p; zero? p => copy q;
		one? p => q + 1;
		d := min(n := degr p, m := degr q);
		cp := coeffs p; cq := coeffs q;
		for i in 1..next d repeat cp.i := cp.i + cq.i;
		m >= (sz := size p) => {
			cp := resize!(cp, sz, next m);
			for i in d+2..next m repeat cp.i := cq.i;
			per [next m, m, cp];
		}
		for i in d+2..next m repeat cp.i := cq.i;
		newDegree!(p, n, m, cp);
	}

	add!(p:%, c:R, q:%):% == {
		one? c => add!(p, q);
		zero? q or zero? c => p;
		zero? p => times!(c, copy q);
		one? p => add!(times!(c, copy q), 1);
		d := min(n := degr p, m := degr q);
		cp := coeffs p; cq := coeffs q;
		for i in 1..next d repeat cp.i := cp.i + c * cq.i;
		m >= (sz := size p) => {
			cp := resize!(cp, sz, next m);
			for i in d+2..next m repeat cp.i := c * cq.i;
			per [next m, m, cp];
		}
		for i in d+2..next m repeat cp.i := c * cq.i;
		newDegree!(p, n, m, cp);
	}

	add!(p:%, c:R, n:Z):% == {
		ASSERT(n >= 0);
		zero? c => p;
		zero? p => monomial(c, n);
		one? p => add!(monomial(c, n), 1);
		cp := coeffs p;
		nn:I := retract n;
		m := degr p;
		nn >= (sz := size p) => {
			cp := resize!(cp, sz, next nn);
			for i in m+2..nn repeat cp.i := 0;
			cp next nn := c;
			per [next nn, nn, cp];
		}
		for i in m+2..nn repeat cp.i := 0;
		cp next nn := cp(next nn) + c;
		newDegree!(p, m, nn, cp);
	}

	-- Partial p = p + c x^h q
	-- For frum <= i <= upto, the i-th coefficient of p will be set to
	-- the i-th coefficient of p + c x^h q. For i < frum and i > upto
	-- the i-th coefficient of p will not change.
	-- frum <= upto
	add!(p:%, c:R, h:Z, q:%, frum:Z, upto:Z):% == {
		ASSERT(h >= 0);
		ASSERT(frum <= upto);
		zero? q => p;
		zero? c => p;
		pp := {
			zero? p or one? p => {
				a := new1 0;
				a.1 := leadingCoefficient p;
				per [1, 0, a];
			}
			p;
		}
		n := degr pp;
		hh:I := retract h;
		hm := hh + degr q;	-- hm = deg(x^h q)
		u := retract upto;
		f := retract frum;
		cp := coeffs pp; cq := coeffs q;
		lp := f; lpplus1 := next lp;
		hp := min(n, u); hpplus1 := next hp;
		lq := max(hh, f); lqplus1 := next lq;
		hq := min(hm, u); hqplus1 := next hq;
		lq > hq =>  pp;
		if (resize?:Boolean := (hq >= (sz := size pp))) then
			cp := resize!(cp, sz, hqplus1);
		if lq > n then
			for i in (next next n)..lq repeat
				cp.i := 0;
		if lp > hp or lq > hp then
			for i in lqplus1..hqplus1 repeat
				cp.i := c * cq(i - hh);
		else {
			high := min(hpplus1, hqplus1);
			for i in max(lpplus1, lqplus1)..high repeat
				cp.i := cp.i + c * cq(i - hh);
			for i in (next high)..hqplus1 repeat
				cp.i := c * cq(i - hh);
		}
		d := computeDegree(max(hq, n), cp);
		resize? => per [hqplus1, d, cp];
		setDegree!(pp, d);
		pp
	}

	generator(p:%):Generator Cross(R, Z) == generate {
		if ~zero? p then {
			v := coeffs p;
			for i in degr p .. 0 by -1 repeat {
				a := v next i;
				if ~zero? a then yield(a, i::Z);
			}
		}
	}

	reverse(p:%):Generator Cross(R, Z) == generate {
		if ~zero? p then {
			v := coeffs p;
			for i in 0 .. degr p repeat {
				a := v next i;
				if ~zero? a then yield(a, i::Z);
			}
		}
	}

	if R has FiniteCharacteristic then {
		pthPower(p:%):% == {
			zero? p => 0;
			dd := charTimes(d := degr p);
			a := new1 dd;
			for i in 1..next dd repeat a.i := 0;
			c := coeffs p;
			for i in 0..d repeat
				a(next charTimes i) := pthPower(c next i)$R;
			per [next dd, dd, a];
		}
	}

	copy(p:%):% == {
		zero? p or one? p => p;
		a := new1(d := degr p);
		c := coeffs p;
		for i in 1..next d repeat a.i := c.i;
		per [next d, d, a];
	}

	copy!(p:%, q:%):% == {
		zero? p or one? p => copy q;
		cp := coeffs p;
		zero? q => {
			cp.1 := 0;
			setDegree!(p, 0);
			p;
		}
		copy!(p, degr q, coeffs q);
	}

	copy!(p:%, d:I, c:Coeffs):% == {
		zero? p or one? p => {
			cp := new1 d;
			for i in 1..next d repeat cp.i := c.i;
			per [next d, d, cp];
		}
		cp := coeffs p;
		d >= (sz := size p) => {
			cp := resize!(cp, sz, next d);
			for i in 1..next d repeat cp.i := c.i;
			per [next d, d, cp];
		}
		for i in 1..next d repeat cp.i := c.i;
		setDegree!(p, d);
		p;
	}

	coefficient(p:%, n:Z):R == {
		ASSERT(n >= 0);
		(m := retract n) > degr p => 0;
		coeffs(p).(next m);
	}

	setCoefficient!(p:%, n:Z, c:R):% == {
		ASSERT(n >= 0);
		zero? p => monomial(c, n);
		m := retract n; mplus1 := next m;
		d := degr p; cp := coeffs p;
		zero? c => {
			m > d => p;
			one? p => { ASSERT(zero? m); 0 }
			cp mplus1 := c;
			setDegree!(p, computeDegree(prev m, cp));
			p;
		}
		one? p => {
			cxn := monomial(c, n);
			zero? n => cxn;
			add!(cxn, p);
		}
		m >= (sz := size p) => {
			cp := resize!(cp, sz, mplus1);
			for i in d..m repeat cp.i := 0;
			cp mplus1 := c;
			per [mplus1, m, cp];
		}
		cp mplus1 := c;		-- guaranteed nonzero
		if m > d then setDegree!(p, m);
		p;
	}

	monomial!(p:%, c:R, n:Z):% == {
		ASSERT(n >= 0);
		zero? p or one? p => monomial(c, n);
		if zero? c then n := 0;
		m := retract n; mplus1 := next m;
		cp := coeffs p;
		m >= (sz := size p) => {
			cp := resize!(cp, sz, mplus1);
			for i in 1..m repeat cp.i := 0;
			cp mplus1 := c;
			per [mplus1, m, cp];
		}
		for i in 1..m repeat cp.i := 0;
		cp mplus1 := c;
		setDegree!(p, m);
		p;
	}

	monomial(c:R, n:Z):% == {
		ASSERT(n >= 0);
		if zero? c then n := 0;
		a := new1(m := retract n);
		for i in 1..m repeat a.i := 0;
		a next m := c;
		per [next m, m, a];
	}

	minus!(p:%):% == {
		zero? p => 0;
		one? p => -1;
		c := coeffs p;
		for i in 1..next degr p repeat c.i := - c.i;
		p;
	}

	-(p:%):% == {
		a := new1(d := degr p);
		c := coeffs p;
		for i in 1..next d repeat a.i := - c.i;
		per [next d, d, a];
	}
		
	reductum(p:%):% == {
		zero?(d := degr p) => 0;
		c := coeffs p;
                per [size p, computeDegree(d - 1, c), c];
	}

	monomial?(p:%):Boolean == {
		c := coeffs p;
		zero?(c.1) and
			(zero?(d := degr p) or zero? computeDegree(prev d, c));
	}

	(x:%) = (y:%):Boolean == {
		degr x ~= (d := degr y) => false;
		cx := coeffs x; cy := coeffs y;
		for i in 1..next d repeat cx.i ~= cy.i => return false;
		true;
	}

	local times!(c:R, a:Coeffs, d:I, b:Coeffs):Coeffs == {
		for i in 1..next d repeat b.i := c * a.i;
		b;
	}

	-- n = upper bound on the actual degree
	local computeDegree(n:I, c:Coeffs):I == {
		ASSERT(n >= 0);
		for i in next n..1 by -1 repeat ~zero?(c.i) => return(i-1);
		0;
	}

	-- newDegree! is for nonintegral domains
	(c:R) * (p:%):% == {
		zero? c => 0; one? c => p;
		d := degr p;
		cf := times!(c, coeffs p, d, new1 d);
		newDegree!(per [next d, d, cf], d, d, cf);
	}

	-- newDegree! is for nonintegral domains
	times!(c:R, p:%):% == {
		zero? c or zero? p => 0;
		one? c => p; one? p => c::%;
		a := coeffs p;
		a := times!(c, a, d := degr p, a);
		newDegree!(p, d, d, a);
	}

	local addsub(p:%, q:%, plus?:Boolean):% == {
		zero? q => p;
		zero? p => {plus? => q; -q }
		M := max(dp := degr p, dq := degr q);
		m := min(dp, dq);
		c := new1 M;
		cp := coeffs p; cq := coeffs q;
		if plus? then for i in 1..next m repeat c.i := cp.i + cq.i;
			else  for i in 1..next m repeat c.i := cp.i - cq.i;
		dp > dq => {
			for i in 2+m..next M repeat c.i := cp.i;
			per [next M, M, c];
		}
		dp < dq => {
			if plus? then for i in 2+m..next M repeat c.i :=   cq.i;
				else  for i in 2+m..next M repeat c.i := - cq.i;
			per [next M, M, c];
		}
		zero?(c, d := computeDegree(M, c)) => 0;
		per [next M, d, c];
	}

	equal?(a:%, b:%, c:%, n:Z):Boolean == {
		import from R;
		n <= 0 or ~single? n => true;
		zero? b or zero? c => {
			(coeff, deg) := trailingMonomial a;
			zero? a or deg >= n;
		}
		m:I := retract n;
		db := degr b; cb := coeffs b;
		dc := degr c; cc := coeffs c;
		M := db + dc;
		for i in 0..min(m, M) repeat {
			z:R := 0;	-- will be coeff(b c, x^i)
			k := min(i, dc);
			for j in i-k .. min(i, db) repeat {
				z := z + cb(next j) * cc(next k);
				k := prev k;
			}
			z ~= coefficient(a, i::Z) => return false;
		}
		for i in next(M)..m repeat
			~zero? coefficient(a, i::Z) => return false;
		true;
	}

	local naiveProduct(p:%, q:%):% == {
		ASSERT(~zero? p); ASSERT(~zero? q);
		ASSERT(~one? p); ASSERT(~one? q);
		dp := degr p;
		dq := degr q;
		M := dp + dq;
		c:Coeffs := new(next M, 0);	-- init all to 0
		times!(c, coeffs p, dp, coeffs q, dq);
		d := { intdom? => M; computeDegree(M, c); }
		per [next M, d, c];
	}

	-- c = c + cp cq
	local times!(c:Coeffs, cp:Coeffs, dp:I, cq:Coeffs, dq:I):() == {
		dq1 := next dq;
		for i in 1..next dp repeat {
			k := i;
			zp := cp.i;	-- coeff(p, x^{i-1})
			if ~zero?(zp) then {
				for j in 1..dq1 repeat {
					if ~zero?(zq := cq.j) then
						c.k := c.k + zp * zq;
					k := next k;
				}
			}
		}
	}
}

#if SUMITTEST
---------------------- test dup.as --------------------------
#include "sumittest"

macro {
        Z == Integer;
        Zx == DenseUnivariatePolynomial(Z, "x");
	Zxt == DenseUnivariatePolynomial(Zx, "t");
}

degree():Boolean == {
	import from Z, Zx;
	x := monom;
	p := (x - 1) * (x + 1);
	degree p = 2 and leadingCoefficient p = 1 and zero? p(-1@Z);
}

exactQuotient():Boolean == {
        import from Zx, Partial Zx;

        x := monom;
	a := x - 1;
	b := x + 1;
	p := a * b;
        q := exactQuotient(p, a);	-- must be b
        f := exactQuotient(p, x);	-- must be failed
        ~(failed? q) and failed? f and retract(q) = b;
}

diff():Boolean == {
	import from Z, Zx, Zxt;
	x:Zx := monom;
	t:Zxt := monom;
	p := x * t + (x^2)::Zxt;
	-- TEMPORARY: NO CONDITIONAL CONSTANTS (969)
	-- D:Derivation(Zxt) := lift(derivation, t);    -- t' = t
	D:Derivation(Zxt) := lift(derivation(), t);    -- t' = t
	q := D p;                       -- must be (1 + x) t + 2 x
	r := q - p;                     -- must be t + 2 x - x^2
	m := x * (x - 2::Zx);
	degree r = 1 and leadingCoefficient r = 1
		and zero?(reductum(r) + m::Zxt);
}

hgcd(a:Zx, b:Zx):Zx == {
	import from Partial Zx, HeuristicGcd(Z, Zx);
	(g, a, b) := heuristicGcd(a, b);
	retract g;
}

mgcd(a:Zx, b:Zx):Zx == {
	import from Partial Zx, ModularUnivariateGcd(Z, Zx);
	(g, a, b) := modularGcd(a, b);
	retract g;
}

heugcd():Boolean == gcd hgcd;

modgcd():Boolean == gcd mgcd;

gcd(ggt:(Zx,Zx) -> Zx):Boolean == {
	import from Z, Zx;

	x := monom;
	p := x^8 + x^6 - 3*x^4 - 3*x^3 + 8*x^2 +2*x - 5@Z ::Zx;
	q := 3*x^6 + 5*x^4 -4*x^2 -9*x + 21@Z ::Zx;
	r := x^2 + 1;
	g := ggt(p, q);
	rg := ggt(r * p, r * q);
	g = 1 and rg = r;
}

print << "Testing dup..." << newline;
sumitTest("degree", degree);
sumitTest("exactQuotient", exactQuotient);
sumitTest("diff", diff);
sumitTest("heugcd", heugcd);
sumitTest("modgcd", modgcd);
print << newline;
#endif

