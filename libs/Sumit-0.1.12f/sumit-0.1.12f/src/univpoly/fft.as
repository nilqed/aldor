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
--------------------------- fft.as ----------------------------------
#include "sumit"

macro {
	I == SingleInteger;
	Z == Integer;
	A == PrimitiveArray;
	POLY == UnivariatePolynomialCategory0(F pretend PrimeFieldCategory0);
}

DiscreteFFT(F:Field): with {
	fftTimes!: (A F, A F, A F, I, F) -> ();
	if F has PrimeFieldCategory0 then {
		fftTimes: (P:POLY) -> (P, P) -> Partial P;
		fftTimes!: (P:POLY) -> (P, P, P) -> Boolean;
	}
} == add {
	-- global buffer for FFT: only grows as needed so we do
	-- not have to allocate a new work buffer for each product.
	macro REC		== Record(siz:I, n:I, n1:F, pow:A F);
	macro RECI		== Record(siz:I, buf:A I);
	macro RECII		== Record(siz:I, log:I, buf:A I);
	local fftWork:REC	== [1, 0, 0, new 1];
	local fftRev:RECII	== [1, 0, new 1];

	-- returns the powers of w buffer already filled
	-- as well as the inverse of N in F
	local fftOmegaBuffer(N:I, w:F):(A F, F) == {
		import from REC;
		ASSERT(even? N);
		wpow := fftWork.pow;
		if N >= fftWork.siz then {       -- must increase buffer
			wpow := resize!(wpow, fftWork.siz, next N);
			fftWork.pow := wpow;
			fftWork.siz := next N;
		}
		if N ~= fftWork.n or w ~= wpow.2 then {
			wpow.1 := 1;
			for i in 2..N repeat wpow.i := w * wpow(prev i);
			wpow(next N) := 1;
			fftWork.n := N;
			fftWork.n1 := inv(N::F);
		}
		(wpow, fftWork.n1);
	}

	-- returns an array rev s.t. rev[i] = 1+reverse(i-1,n)
	local fftReverseIndex(n:I, N:I):A I == {
		ASSERT(2^n = N);
		import from RECI;
		buffer := fftRev.buf;
		s := fftRev.siz;
		l := fftRev.log;
		N = s and n = l => buffer;
		if N > s then {
			buffer := resize!(buffer, s, N);
			fftRev.buf := buffer;
			fftRev.siz := N;
		}
		for i in 1..N repeat buffer.i := next reverse(prev i, n);
		buffer;
	}

	-- changes b_n ... b_1  into  b_1 ... b_n
	local reverse(a:I, n:I):I == {
		b:I := 0;
		for i in 1..n repeat {
			b := shift(b, 1);
			if bit(a, 0) then b := next b;
			a := shift(a, -1);
		}
		b;
	}

	if F has PrimeFieldCategory0 then {
		local charac:I		== retract(characteristic$F);
		local kcoeff:Z		== (prev(charac::Z))^2;
		-- global buffer for FFT: only grows as needed so we do
		-- not have to allocate a new work buffer for each product.
		local ffta:RECI		== [1, new 1];
		local fftb:RECI		== [1, new 1];
		local fftab:RECI	== [1, new 1];

		local fftBuffer!(rec:RECI, N:I, zr?:Boolean):A I == {
			buffer := rec.buf;
			if N > rec.siz then {
				buffer := resize!(buffer, rec.siz, N);
				rec.buf := buffer;
				rec.siz := N;
			}
			if zr? then for i in 1..N repeat buffer.i := 0;
			buffer;
		}

		-- returns (n, N, q, w, toosmall?) where
		--   N = 2^n is stricly greater than d
		--   q = N k + 1 for k odd is a Fourier prime
		--   w is a primitive N-th root of unity modulo q
		--   toosmall? is true if q is too small for the
		--   given combination of degree and characteristic
		-- [Should then return a list of primes whose product is large]
		local getPrime(d:I):(I, I, I, I, Boolean) == {
			import from Z;
			ASSERT(d > 1);
			n := length d;
			N := shift(1@I, n);
			ASSERT(N = 2^n); ASSERT(N > d);
			minq := next(N quo 2)::Z * kcoeff;
			(q, w) := fourierPrime(n)$HalfWordSizePrimes;
			-- TEMPORARY: THOSE PRIMES ARE TOO SLOW!
			-- if q::Z < minq then
				-- (q,w):= fourierPrime(n)$WordSizePrimes;
			TRACE("fft::getPrime: q = ", q);
			TRACE("fft::getPrime: omega = ", w);
			(n, N, q, w, (q::Z) < minq);
		}

		-- returns false if ok, true if error
		-- replaces ans by ans + a*b, a and b are left unchanged
		fftTimes!(P:POLY):(P, P, P) -> Boolean == {
			(ans:P, a:P, b:P):Boolean +-> {
				import from Z, F, DiscreteFFTModuloP;
				START__TIME;
				d:I := retract(degree a + degree b);
				(ln, N, q, w, small?) := getPrime d;
				small? => true;
				ab := fftBuffer!(fftab, N, false);
				fftTimes!(P)(ln, N, ab, q, w, a, b);
				TIME("fft::fftTimes!: fft product at ");
				for i in 1..next d | ~zero?(cc := ab.i) repeat
					ans := add!(ans, cc::F, prev(i)::Z);
				TIME("fft::fftTimes!: product rebuilt at ");
				false;
			}
		}

		-- returns a*b or failed
		fftTimes(P:POLY):(P, P) -> Partial P == {
			import from Z, F, DiscreteFFTModuloP;
			(a:P, b:P):Partial P +-> {
				START__TIME;
				d:I := retract(degree a + degree b);
				(ln, N, q, w, small?) := getPrime d;
				small? => failed;
				-- ab := fftBuffer!(fftab, N, false);
				ab := fftBuffer!(fftab, N, true);
				fftTimes!(P)(ln, N, ab, q, w, a, b);
				TIME("fft::fftTimes: fft product at ");
				ans:P := monomial(ab(next d)::F, d::Z);
				for i in 1..d | ~zero?(cc := ab.i) repeat
					ans := add!(ans, cc::F, prev(i)::Z);
				TIME("fft::fftTimes: product rebuilt at ");
				[ans];
			}
		}

		local fftTimes!(P:POLY)(ln:I,N:I,ab:A I,q:I,w:I,a:P,b:P):() == {
				import from DiscreteFFTModuloP;
				rev := fftReverseIndex(ln, N);
				aa := fftBuffer!(ffta, N, true);
				bb := fftBuffer!(fftb, N, true);
				-- do the bit-shuffling while copying the polys
				for term in a repeat {
					(c, e) := term;
					aa(rev next retract e) := lift(c)$F;
				}
				for term in b repeat {
					(c, e) := term;
					bb(rev next retract e) := lift(c)$F;
				}
				fftTimes!(ab, aa, bb, rev, ln, N, w, q);
		}
	}

	-- stores the result in ab but also trashes a and b
	fftTimes!(ab:A F, a:A F, b:A F, N:I, w:F):() == {
		ASSERT(N > 1);
		n := length prev N;
		ASSERT(N = 2^n);
		rev := fftReverseIndex(n, N);
		(wpow, N1) := fftOmegaBuffer(N, w);
		for i in 1..N repeat ab(rev i) := a.i;	-- ab = bit-shuffle a
		fft!(ab, n, N, wpow, false);		-- ab = FFT(a)
		for i in 1..N repeat a(rev i) := ab.i;	-- a = bit-shuffle b
		fft!(a, n, N, wpow, false);		-- a = FFT(b)
		-- bit shuffle product while building it
		for i in 1..N repeat b(rev i) := ab.i * a.i;
		fft!(b, n, N, wpow, true);		-- inverse FFT
		for i in 1..N repeat ab.i := N1 * b.i;
	}

	-- computes FFT(a) in-place
	-- w = [w_0,w_1,...,w_{N-1},w_N] is such that
	-- w_1 is a primitive N-th root of unity and w_k = w_1^k
	-- the 1 on the right-side is for reversing, right-to left is w^{-1}
	-- a must be already bit-shuffled upon entry
	local fft!(a:A F, n:I, N:I, w:A F, reverse?:Boolean):A F == {
		ASSERT(2^n = N); ASSERT(w.1 = 1); ASSERT(w(next N) = 1);
		m2:I := 1;
		f:I := 1;
		e := N;
		if reverse? then { f := next N; e := -N; }
		for s in 1..n repeat {
			m := shift(m2, 1);
			e := shift(e, -1);
			ASSERT(m = 2^s); ASSERT(m * abs(e) = N);
			i := f;
			for j in 1..m2 repeat {
				k := j;
				while k < N repeat {
					t := w.i * a(k + m2);
					a(k + m2) := a.k - t;
					a.k := a.k + t;
					k := k + m;
				}
				i := i + e;
			}
			m2 := m;
		}
		a;
	}
}
