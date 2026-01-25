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
------------------------ sit_matquot.as ---------------------------
-- Copyright (c) Manuel Bronstein 1997
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1997
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I == MachineInteger;
	Z == Integer;
	V == Vector;
}

#if ALDOC
\thistype{MatrixCategoryOverFraction}
\History{Manuel Bronstein}{16/6/97}{created}
\Usage{import from \this(R, MR, Q, MQ)}
\Params{
{\em R} & \astype{IntegralDomain} & an integral domain\\
{\em MR} & \astype{MatrixCategory} R & a matrix type over R\\
{\em Q} & \astype{FractionCategory} R & a fraction domain of R\\
{\em MQ} & \astype{MatrixCategory} Q & a matrix type over Q\\
}
\Descr{\this(R, MR, Q, MQ) provides useful conversions between
matrices with integral and rational coefficients.}
\begin{exports}
\category{\astype{LinearCombinationFraction}(R, MR, Q, MQ)}\\
\asexp{makeColIntegral}:
& (MQ, I) $\to$ (R, V R) & Convert to an integral column\\
\asexp{makeRowIntegral}: & (MQ, I) $\to$ (R, V R) & Convert to an integral row\\
\asexp{makeRowIntegral}:
& MQ $\to$ (V R, MR) & Convert to an integral matrix row by row\\
\end{exports}
\begin{exports}[if Q has \astype{FractionByCategory0} R]
\asexp{makeRowIntegralBy}:
& MQ $\to$ (V Z, MR) & Convert to an integral matrix row by row\\
\end{exports}
\begin{aswhere}
I &==& \astype{MachineInteger}\\
Z &==& \astype{Integer}\\
V &==& \astype{Vector}\\
\end{aswhere}
#endif

MatrixCategoryOverFraction(R:IntegralDomain, MR:MatrixCategory R,
	Q:FractionCategory R, MQ:MatrixCategory Q):
	LinearCombinationFraction(R, MR, Q, MQ) with {
		makeColIntegral: (MQ, I) -> (R, V R);
#if ALDOC
\aspage{makeColIntegral}
\Usage{(a, v) := \name(B, i)}
\Signature{(MQ, \astype{MachineInteger})}{(R, \astype{Vector} R)}
\Params{
{\em B} & MQ & A matrix with rational coefficients\\
{\em i} & \astype{MachineInteger} & A column index\\
}
\Retval{Returns $(a, v)$ such that $v = a$ times the $\sth{i}$ column of $B$,
and $v$ has integral coefficients.
If R is a \astype{GcdDomain}, then $v$ is primitive.}
#endif
		makeRowIntegral: MQ -> (V R, MR);
		makeRowIntegral: (MQ, I) -> (R, V R);
#if ALDOC
\aspage{makeRowIntegral}
\Usage{(v, A) := \name~B\\(a, v) := \name(B, i)}
\Signatures{
\name: & MQ $\to$ (\astype{Vector} R, MR)\\
\name: & (MQ, \astype{MachineInteger}) $\to$ (R, \astype{Vector} R)\\
}
\Params{
{\em B} & MQ & A matrix with rational coefficients\\
{\em i} & \astype{MachineInteger} & A row index\\
}
\Retval{\name(B) returns $(v, A)$ such that $A$ has integral coefficients
and the $\sth{j}$ row of $A$ is equal to $v.j$ times the $\sth{j}$ row of $B$
for each $j$, while
\name(B, i) returns $(a, v)$ such that $v$ has integral coefficients
and $v$ equals $a$ times the $\sth{i}$ row of $B$.
If R is a \astype{GcdDomain}, then each row of $A$ (resp.~$v$) is primitive.}
#endif
		if Q has FractionByCategory0 R then {
			makeRowIntegralBy: MQ -> (V Z, MR);
#if ALDOC
\aspage{makeRowIntegralBy}
\Usage{(v, A) := \name~B}
\Params{ {\em B} & MQ & A matrix with rational coefficients\\ }
\Retval{Returns $(v, A)$ such that $A$ has integral coefficients
and the $\sth{j}$ row of $A$ is equal to the $\sth{j}$ row of $B$
shifted by $v.j$.}
#endif
		}
} == add {
	local gcd?:Boolean == R has GcdDomain;

	makeRowIntegral(B:MQ, r:I):(R, V R) == {
		import from VectorOverFraction(R, Q);
		makeIntegral row(B, r);
	}

	makeColIntegral(B:MQ, c:I):(R, V R) == {
		import from VectorOverFraction(R, Q);
		makeIntegral column(B, c);
	}

	-- Most of those functions use the fact that IntegralDomain's are
        -- commutative (if fractions of noncommutative domains are used
        -- one day, those functions must be recoded, as they will give
	-- incorrect results if R is not commutative).

	(x:Q) * (A:MR):MQ == {
		import from I;
		(r, c) := dimensions A;
		B:MQ := zero(r, c);
		for i in 1..r repeat for j in 1..c repeat B(i,j) := A(i,j) * x;
		B;
	}

	makeRational(A:MR):MQ == {
		import from I, Q;
		(r, c) := dimensions A;
		B:MQ := zero(r, c);
		for i in 1..r repeat for j in 1..c repeat B(i,j) := A(i,j)::Q;
		B;
	}

	if Q has FractionFieldCategory0 R then {
		normalize(A:MR):(R, MQ) == {
			import from I, Q;
			(r, c) := dimensions A;
			B:MQ := zero(r, c);
			zero? r or zero? c => (1, B);
			a := A(1, 1);
			for i in 1..r repeat for j in 1..c repeat
				B(i,j) := A(i,j) / a;
			(a, B);
		}
	}

	local prod(l:List R):R == {
		r:R := 1;
		while ~empty? l repeat {
			r := times!(r, first l);
			l := rest l;
		}
		r;
	}

	-- common denominator for row i
	local denom(B:MQ, r:I):R == {
		import from Q, List R;
		denoms := [denominator(B(r, j)) for j in 1..numberOfColumns B];
		gcd? => lcm(denoms)$(R pretend GcdDomain);
		prod denoms;
	}

	makeIntegral(B:MQ):(R, MR) == {
		import from I, R, Q, List R;
		(r, c) := dimensions B;
		denoms := [denom(B, i) for i in 1..r];
		d := { gcd? => lcm(denoms)$(R pretend GcdDomain); prod denoms; }
		A:MR := zero(r, c);
		for i in 1..r repeat for j in 1..c repeat
			A(i,j) := numerator(d * B(i,j));
		(d, A);
	}

	local makeRowIntegral!(A:MR, v:V R, B:MQ, r:I):() == {
		import from I, Q;
		c := numberOfColumns B;
		assert(c <= numberOfColumns A);
		assert(r > 0); assert(r <= numberOfRows A);
		v.r := denom(B, r);
		for j in 1..c repeat A(r, j) := numerator(v.r * B(r, j));
	}

	makeRowIntegral(B:MQ):(V R, MR) == {
		import from I, V R;
		(r, c) := dimensions B;
		A:MR := zero(r, c);
		v:V R := zero r;
		for i in 1..r repeat makeRowIntegral!(A, v, B, i);
		(v, A);
	}

	if Q has FractionByCategory0 R then {
		-- returns mu s.t. p^(-mu) * row i is integral
		local order(B:MQ, r:I):Z == {
			import from Boolean, Q;
			mu:Z := 0;
			for j in 1..numberOfColumns B |~zero?(b:=B(r,j)) repeat{
				m:Z := order(b)$Q;
				if m < mu then mu := m;
			}
			assert(mu <= 0);
			mu;
		}

		local makeRowIntegral!(A:MR, v:V Z, B:MQ, r:I):() == {
			import from I, Z, Q;
			c := numberOfColumns B;
			assert(c <= numberOfColumns A);
			assert(r > 0); assert(r <= numberOfRows A);
			v.r := - order(B, r);
			for j in 1..c repeat
				A(r, j) := numerator shift(B(r, j), v.r);
		}

		makeRowIntegralBy(B:MQ):(V Z, MR) == {
			import from I, V Z;
			(r, c) := dimensions B;
			A:MR := zero(r, c);
			v:V Z := zero r;
			for i in 1..r repeat makeRowIntegral!(A, v, B, i);
			(v, A);
		}

		makeIntegralBy(B:MQ):(Z, MR) == {
			import from I, Z, Q;
			mu:Z := 0;
			(r, c) := dimensions B;
			for i in 1..r repeat {
				m := order(B, i);
				if m < mu then mu := m;
			}
			assert(mu <= 0);
			A:MR := zero(r, c);
			for i in 1..r repeat for j in 1..c repeat
				A(i, j) := numerator shift(B(i, j), -mu);
			(mu, A);
		}
	}
}
