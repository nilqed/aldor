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
------------------------------ sympow2.as ------------------------------
#include "sumit"

macro Z	== Integer;

SecondOrderSymmetricPower(R:IntegralDomain,
	L:LinearOrdinaryDifferentialOperatorCategory0 R): with {
		symmetricPower: (L, Z) -> L;
} == add {
	local gcd?:Boolean	== R has GcdDomain;

	if R has GcdDomain then {
		local rgcd(a:R, b:R):R			== gcd(a, b);
		local rgcdquo(a:R, b:R):(R, R, R)	== gcdquo(a, b);

		local primpart(op:L):L == {
			START__TIME;
			op := primitivePart op;
			TIME("sympow2::primpart: primitive part at ");
			op;
		}

	}

	symmetricPower(op:L, n:Z):L == {
		ASSERT(n > 0);
		ASSERT(degree op = 2);
		import from R, Partial R;
		TRACE("symmetricPower, op = ", op);
		TRACE("n = ", n);
		one? n => op;
		p := leadingCoefficient op;
		failed?(u := reciprocal p) => ffsympow(op, n, p);
		sympow(op, n, retract u);
	}

	-- case where the leading coeff of L is invertible
	-- ainv = inverse of leading coeff
	-- can then perform the iteration in R
	local sympow(op:L, n:Z, ainv:R):L == {
		TRACE("symmetricPower, op = ", op);
		TRACE("n = ", n);
		TRACE("ainv = ", n);
		ASSERT(n > 1);
		a := ainv * coefficient(op, 1);
		aa := a::L;
		b := ainv * coefficient(op, 0);
		D:L := monom;
		-- the basic iteration is L0 = 1, L1 = pD,
		--  L_{i+1} = D L_i + i a L_i + i (m-(i-1)) b L_{i-1}
		L1 := D;
		L2 := D^2 + a * D + (n * b)::L;
		for i in 2..n repeat {
			L3 := (D + i * aa) * L2;
			L3 := add!(L3, i * (n - prev i) * b, L1);
			L1 := L2;
			L2 := L3;
		}
		ASSERT(degree L2 = next n);
		L2;
	}

	-- case where the leading coeff p of L is not invertible
	local ffsympow(op:L, n:Z, p:R):L == {
		import from Derivation R;
		ASSERT(n > 1);
		START__TIME;
		a := coefficient(op, 1);
		bnz? := ~zero?(b := coefficient(op, 0));
		DR := derivation$L;
		Dp := DR p;
		ampp := a - Dp;
		-- e = gcd(p, p', a - p')   o = gcd(e, b p/e)
		e:R := 1; o:R := 1;
		-- pe = p / e     dpe = p' / e
		pe := p;  dpe := Dp;
		if gcd? then {
			(e, pe, dpe) := rgcdquo(p, Dp);
			if ~zero?(ampp) then {
				e := rgcd(e, ampp);
				pe := quotient(p, e);
				dpe := quotient(Dp, e);
			}
			if bnz? then o := rgcd(e, b * pe);
		}
		-- amppe = (a - p') / e
		amppe := quotient(ampp, e);
		-- loge = p / e  e' / e  +  p / e  o' / o
		loge := quotient(pe * DR e, e) + quotient(pe * DR o, o);
		-- po = p / o     dpo = p' / o     amppo = (a - p') / o
		-- logo = p / o  e' / e  +  p / o  o' / o   logo1 = p/o e'/e
		po := pe;
		dpo := dpe;
		coefo := dpo;
		amppo := amppe;
		logo := loge;
		if gcd? and bnz? then {
			po := quotient(p, o);
			amppo := quotient(ampp, o);
			dpo := quotient(Dp, o);
			logo1 := quotient(po * DR e, e);
			logo := logo1 + quotient(po * DR o, o);
			coefo := dpo + logo1;
		}
		coefP1 := quotient(b * pe, o);		-- (p b) / (e o)
		TIME("ffsympow::symmetricPower: recurrence coefficients at ");
		D:L := monom;
		P1 := p * D^2 + a * D + (n * b)::L;
		P2 := (pe*D + (2*amppe+dpe)::L) * P1 + ((2 * prev n)*pe*b) * D;
		for i in 3..n repeat {
			local coefP2, coefDP2:R; local P3:L;
			j := prev(i quo 2);	-- either i/2 - 1 or (i-1)/2 - 1
			if even? i then {
				coefDP2 := pe;
				coefP2 := i * amppe + j * loge + dpe;
			}
			else {
				coefDP2 := po;
				coefP2 := i * amppo + j * logo + coefo;
			}
			P3 := (coefDP2 * D + coefP2::L) * P2;
			if bnz? then
				P3 := add!(P3, (i * (n - prev i)) * coefP1, P1);
			P1 := P2;
			P2 := P3;
		}
		ASSERT(degree P2 = next(n::Z));
		TIME("sympow2::symmetricPower: non-primitive operator at ");
		gcd? => primpart P2;
		P2;
	}
}
