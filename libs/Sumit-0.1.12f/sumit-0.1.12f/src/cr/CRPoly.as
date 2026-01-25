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
---------------------------------- CRPoly.as -------------------------
#include "sumit"

CRPoly (R: SumitRing, P: UnivariatePolynomialCategory R): with {
	macro Px  == DenseUnivariatePolynomial (R, "x");
	macro Ph  == DenseUnivariatePolynomial (Px, "h");
	macro PRh == DenseUnivariatePolynomial (R, "h");
	
	create: P -> %;
	generator:   % -> Generator Ph;
	generator:   (%, R, R) -> Generator R;
	generator:   (%, R) -> Generator Px;
	generatorx:   (%, R) -> Generator PRh;
	<<:          (TextWriter, %) -> TextWriter;
} == add {
	macro Z   == Integer;
	macro SI  == SingleInteger;
	macro Px  == DenseUnivariatePolynomial (R, "x");
	macro Ph  == DenseUnivariatePolynomial (Px, "h");
	macro PRh == DenseUnivariatePolynomial (R, "h");
	macro Rep == Array Ph;
	
	import from R, Z, SI, Px, Ph, Rep;
	
	macro CIN == Array Rep;
	import from CIN;
	
	local x: Px == monomial(1,1);
	local h: Ph == monomial(1,1);
	
	local Cin (cin: CIN, i: SI, n: SI): () == {
		local k,l: SI;
		k := 1+ i mod 2; l := 1+ (i+1) mod 2;
		(cin.k).(i+1) := factorial(i::Integer)::Px * h^(i::Integer);
		for j in i+1..n repeat {
			(cin.k).(j+1) := i::Px * h * (cin.l).j 
			+ (x::Ph + i::Px * h)*(cin.k).j;
		}
	}
	
	create (p: P): % == {
		macro CRC == PrimitiveArray R;
		
		import from CRC;
		
		local deg: SI;	
		local cr: Rep;
		local crc: CRC;
		local coef: R;
		local k: SI;
		
		deg := (degree p):: SI;
		cr := new (deg+1, monomial(monomial(0,0),0));
		crc := new (deg+1, 0);
		cin := new (2, empty());
		cin.1 := new (deg+1, monomial(monomial(0,0),0));
		cin.2 := new (deg+1, monomial(monomial(0,0),0));
		for i in 0..deg repeat
			crc.(i+1) := coefficient (p, i::Integer);
		(cin.1).1 := 1;
		for i in 2..deg+1 repeat 
			(cin.1).i := (x^(i-1)::Integer)::Ph;
		for i in 0..deg repeat {
			k := 1+ i mod 2;
			for j in i..deg repeat {
				coef := crc.(j+1);
				if coef ~= 0 then {
					cr.(i+1) := cr.(i+1) + coef::Px*(cin.k).(j+1);
				}
			}
			Cin (cin, i+1, deg);
		}
		per cr;
	}
	
	generator (Cr: %): Generator Ph == generate {
		macro PRh == Array Ph;
		
		import from PRh;
		
		local a: PRh;
		local cr: Rep := rep Cr;
		
		a := new (#cr, 0);
		for i in 1..#cr repeat
			a.i := cr.i;
		repeat {
			yield a.1;
			for i in 1..#a-1 repeat
				a.i := a.i + a.(i+1);
		}
	}

	generator (Cr: %, x0: R, h: R): Generator R == generate {
		local a: Array R;
		local cr: Rep := rep Cr;
		
		a := new (#cr, 0);
		for i in 1..#cr repeat 
			a.i := cr.i(h::Px)(x0);
		repeat {
			yield a.1;
			for i in 1..#a-1 repeat
				a.i := a.i + a.(i+1);
		}
	}
	
	generator (Cr: %, h: R): Generator Px == generate {
		local a: Array Px;
		local cr: Rep := rep Cr;
		
		a := new (#cr, 0);
		for i in 1..#cr repeat
			a.i := cr.i(h::Px);
		repeat {
			yield a.1;
			for i in 1..#a-1 repeat
				a.i := a.i + a.(i+1);
		}
	}
	
	generatorx (Cr: %, x0: R): Generator PRh == generate {
		local h: PRh == monomial(1,1);
		local a: Array PRh;
		local cr: Rep := rep Cr;
		
		a := new (#cr, 0); 
		for i in 1..#cr repeat {
			for j in 0..(degree cr.i) repeat 
				a.i := a.i + apply (coefficient (cr.i, j::Integer),x0)*h^j;
		}
		repeat {
			yield a.1;
			for i in 1..#a-1 repeat 
				a.i := a.i + a.(i+1);
		}
	}

						
	(p: TextWriter) << (cr: %): TextWriter == {
		p << "\{" << (rep cr).1;
		for i in 2..# rep cr repeat 
			p << ",+," << (rep cr).i;
		p << "\}";
	}
}


#if TEST
---- test CRPoly

Test(): () == {
	macro P  == DenseUnivariatePolynomial (Integer, "x");
	macro Ph == DenseUnivariatePolynomial (Integer, "h");
	macro Pxh == DenseUnivariatePolynomial (P, "h");
	macro CR == CRPoly (Integer, P);
	macro A  == Array Integer;
	macro CRG == Generator Integer;
	macro CRH == Generator P;
	macro CRX == Generator Ph;
	macro CRXH == Generator Pxh;

	import from A, P, CR, Integer, CRG, CRH, CRX, CRXH;

	local x: P == monomial (1,1);
	local cr: CR;
	local p: P;
	local crh: CRH;
	local p: P;
	local ph: Ph;
	local crx: CRX;
	local crxh: CRXH;
	local pxh: Pxh;
	local v, t : Integer;

	p := x^3;
	cr := create p;
	print << "$" << p << "$ CR:  $" << cr << "$" << newline << newline;

	crg := generator (cr, 3, 1);
	for i in 1..10 repeat {
		step! crg; v := value crg; t := (3+(i-1)*1)^3;
		print << v << "   "; 
		print << "$x^3 (x=3), h=1:$ " << t;
		if v ~= t then print << "  ERROR";
		else print << "  passed";
		print << newline << newline;
	}	
	
	print << newline;
	
	crh := generator (cr, 1);
	for i in 1..10 repeat {
		step! crh; p := value crh; 
		v := apply (p, 3); t := (3+(i-1)*1)^3;
		print << "$" << p << " = " << v << "$";
		if v ~= t then print << "  ERROR";
		else print << "  passed";
		print << newline << newline;
	}	
	
	print << newline;
	
	crx := generatorx (cr, 3);
	for i in 1..10 repeat {
		step! crx; ph := value crx; 
		v:= apply (ph,1); t := (3+(i-1)*1)^3;
		print << "$" << ph << " = " << v << "$";
		if v ~= t then print << "  ERROR";
		else print << "  passed";
		print << newline << newline;
	}		
	
	print << newline;
	
	crxh := generator cr;
	for i in 1..10 repeat {
		step! crxh; pxh := value crxh; 
		v := pxh(1::P)(3); t := (3+(i-1)*1)^3;
		print << "$" << pxh << " = " << v << "$";
		if v ~= t then print "  ERROR";
		else print << "  passed";
		print << newline << newline;
	}
}

print << "Testing CRPoly..." << newline << newline;
Test();

#endif

