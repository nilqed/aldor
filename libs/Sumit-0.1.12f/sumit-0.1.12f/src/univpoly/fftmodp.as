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
--------------------------- fftmodp.as ----------------------------------
#include "sumit"

macro {
	I == SingleInteger;
	A == PrimitiveArray I;
}

DiscreteFFTModuloP: with {
	fftTimes!: (A, A, A, A, I, I, I, I) -> ();
} == add {
	-- global power of omega buffer for FFT (grows as needed)
	macro REC		== Record(siz:I, n:I, n1:I, md:I, pow:A);
	local fftWork:REC	== [1, 0, 0, 0, new 1];
	local maxhalf:I		== maxPrime$HalfWordSizePrimes;

	-- returns the powers of w buffer already filled
	-- as well as the inverse of N modulo p
	local fftOmegaBuffer(N:I, w:I, p:I):(A, I) == {
		import from REC;
		ASSERT(even? N);
		wpow := fftWork.pow;
		if N >= fftWork.siz then {	-- must increase buffer
			wpow := resize!(wpow, fftWork.siz, next N);
			fftWork.pow := wpow;
			fftWork.siz := next N;
		}
		if N ~= fftWork.n or w ~= wpow.2 or p ~= fftWork.md then {
			wpow.1 := 1;
			if p > maxhalf then
				for i in 2..N repeat
					wpow.i := mod_*(w, wpow(prev i), p);
			else
				for i in 2..N repeat
					wpow.i := (w * wpow(prev i)) rem p;
			wpow(next N) := 1;
			fftWork.n := N;
			fftWork.n1 := mod_/(1, N, p);
			fftWork.md := p;
		}
		(wpow, fftWork.n1);
	}

	-- stores the result in ab but also trashes a, and b
	-- expects the inputs a and b to be already bit-shuffled
	-- r is an array s.t. r[i] = 1+bit-reverse(i-1,n)
	-- p is the modulus (a Fourier prime of the form 2^N k + 1)
	-- w is a primitive N-th root of unity modulo p
	fftTimes!(ab:A, a:A, b:A, r:A, n:I, N:I, w:I, p:I):() == {
		ASSERT(N = 2^n); ASSERT(n > 0);
		(wpow, N1) := fftOmegaBuffer(N, w, p);
		p > maxhalf => ftimes!(ab, a, b, r, n, N, N1, wpow, p);
		htimes!(ab, a, b, r, n, N, N1, wpow, p);
	}

	local htimes!(ab:A, a:A, b:A, rev:A, n:I, N:I, N1:I, w:A, p:I):() == {
		ASSERT(((N * N1) rem p) = 1);
		ASSERT(((w.2 * w.N) rem p) = 1);
		ASSERT(2^n = N);
		hfft!(a, n, N, w, p, false);		-- a = FFT(a)
		hfft!(b, n, N, w, p, false);		-- b  = FFT(b)
		-- bit-shuffle ab while building it
		for i in 1..N repeat ab(rev i) := (a.i * b.i) rem p;
		hfft!(ab, n, N, w, p, true);		-- inverse FFT
		for i in 1..N repeat ab.i := (N1 * ab.i) rem p;
	}

	local ftimes!(ab:A, a:A, b:A, rev:A, n:I, N:I, N1:I, w:A, p:I):() == {
		ASSERT(mod_*(N, N1, p) = 1);
		ASSERT(mod_*(w.2, w.N, p) = 1);
		ASSERT(2^n = N);
		ffft!(a, n, N, w, p, false);		-- a = FFT(a)
		ffft!(b, n, N, w, p, false);		-- b  = FFT(b)
		-- bit-shuffle ab while building it
		for i in 1..N repeat ab(rev i) := mod_*(a.i, b.i, p);
		ffft!(ab, n, N, w, p, true);		-- inverse FFT
		for i in 1..N repeat ab.i := mod_*(N1, ab.i, p);
	}

	-- computes FFT(a) in-place
	-- w = [w_0,w_1,...,w_{N-1},w_N] is such that
	-- w_1 is a primitive N-th root of unity and w_k = w_1^k
	-- the 1 on the right-side is for reversing, right-to left is w^{-1}
	-- a must be already bit-shuffled upon entry
	local hfft!(a:A, n:I, N:I, w:A, p:I, reverse?:Boolean):A == {
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
					t := (w.i * a(k + m2)) rem p;
					a(k + m2) := mod_-(a.k, t, p);
					a.k := mod_+(a.k, t, p);
					k := k + m;
				}
				i := i + e;
			}
			m2 := m;
		}
		a;
	}

	local ffft!(a:A, n:I, N:I, w:A, p:I, reverse?:Boolean):A == {
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
					t := mod_*(w.i, a(k + m2), p);
					a(k + m2) := mod_-(a.k, t, p);
					a.k := mod_+(a.k, t, p);
					k := k + m;
				}
				i := i + e;
			}
			m2 := m;
		}
		a;
	}
}
