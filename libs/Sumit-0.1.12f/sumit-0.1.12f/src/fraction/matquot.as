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
------------------------ matquot.as ---------------------------
-- Copyright Manuel Bronstein, 1997-1998
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1997
-- Copyright INRIA, 1998

#include "sumit"

macro {
	I == SingleInteger;
	V == Vector;
}

#if ASDOC
\thistype{MatrixCategoryOverQuotient}
\History{Manuel Bronstein}{16/6/97}{created}
\Usage{import from \this(R, MR, Q, MQ)}
\Params{
{\em R} & IntegralDomain & an integral domain\\
{\em MR} & MatrixCategory0 R & a matrix type over R\\
{\em Q} & QuotientCategory R & a quotient of R\\
{\em MQ} & MatrixCategory0 Q & a matrix type over Q\\
}
\Descr{\this(R, MR, Q, MQ) provides useful conversions between
matrices with integral and rational coefficients.}
\begin{exports}
$*$: & (Q, MR) $\to$ MQ & product of a fraction by an integral matrix\\
makeColIntegral: & (MQ, Z) $\to$ (R, Vector R)
& conversion to an integral column\\
makeIntegral: & MQ $\to$ (R, MR) & conversion to an integral matrix\\
makeRational: & MR $\to$ MQ & conversion to a rational matrix\\
makeRowIntegral: & (MQ, Z) $\to$ (R, Vector R)
& conversion to an integral row\\
makeRowIntegral: & MQ $\to$ MR & conversion to an integral matrix row by row\\
\end{exports}
\begin{aswhere}
Z &==& SingleInteger\\
\end{aswhere}
\begin{exports}[if Q has QuotientFieldCategory0 R]
normalize: & MR $\to$ (R, MQ) & conversion to a monic rational matrix\\
\end{exports}
#endif

MatrixCategoryOverQuotient(R:IntegralDomain,
	MR:MatrixCategory0 R,Q:QuotientCategory R,MQ:MatrixCategory0 Q): with {
	*: (Q, MR) -> MQ;
#if ASDOC
\aspage{$*$}
\Usage{c~\name~A}
\Signature{(Q, MR)}{MQ}
\Params{
{\em c} & Q & A quotient\\
{\em A} & MR & A matrix with integral coefficients\\
}
\Retval{Returns $c A$ as a matrix with rational coefficients.}
#endif
	makeColIntegral: (MQ, I) -> (R, V R);
#if ASDOC
\aspage{makeColIntegral}
\Usage{(a, v) := \name(B, i)}
\Signature{(MQ, SingleInteger)}{(R, Vector R)}
\Params{
{\em B} & MQ & A matrix with rational coefficients\\
{\em i} & SingleInteger & A column index\\
}
\Retval{Returns $(a, v)$ such that $v = a$ times the $\sth{i}$ column of $B$,
and $v$ has integral coefficients.
If R is a GcdDomain, then $v$ is primitive.}
\seealso{makeIntegral(\this), makeRowIntegral(\this)}
#endif
	makeIntegral: MQ -> (R, MR);
#if ASDOC
\aspage{makeIntegral}
\Usage{(a, A) := \name~B}
\Signature{MQ}{(R, MR)}
\Params{ {\em B} & MQ & A matrix with rational coefficients\\ }
\Retval{Returns $(a, A)$ such that $A = a B$ has integral coefficients.
If R is a GcdDomain, then $A$ is primitive.}
\seealso{makeColIntegral(\this)\\ makeRowIntegral(\this)}
#endif
	makeRowIntegral: MQ -> MR;
	makeRowIntegral: (MQ, I) -> (R, V R);
#if ASDOC
\aspage{makeRowIntegral}
\Usage{\name~B\\(a, v) := \name(B, i)}
\Signatures{
\name: & MQ $\to$ MR\\
\name: & (MQ, SingleInteger) $\to$ (R, Vector R)\\
}
\Params{
{\em B} & MQ & A matrix with rational coefficients\\
{\em i} & SingleInteger & A row index\\
}
\Retval{\name(B) returns a matrix $A$ with integral coefficients such that
each row of $A$ is a multiple of the corresponding row of $B$, while
\name(B, i) returns $(a, v)$ such that $v = a$ times the $\sth{i}$ row of $B$,
and $v$ has integral coefficients.
If R is a GcdDomain, then each row of $A$ (resp.~$v$) is primitive.}
\seealso{makeColIntegral(\this), makeIntegral(\this)}
#endif
	makeRational: MR -> MQ;
#if ASDOC
\aspage{makeRational}
\Usage{\name~A}
\Signature{MR}{MQ}
\Params{ {\em A} & MR & A matrix with integral coefficients\\ }
\Retval{Returns $A$ as a matrix with rational coefficients.}
#endif
	if Q has QuotientFieldCategory0 R then {
		normalize: MR -> (R, MQ);
#if ASDOC
\aspage{normalize}
\Usage{(a, B) := \name~A}
\Signature{MR}{(R, MQ)}
\Params{ {\em A} & MR & A matrix with integral coefficients\\ }
\Retval{Returns $(a, B)$ such that $A = a B$ and $B$ has
rational coefficients and the top-left element of $B$ is $1$.}
#endif
	}
} == add {
	local gcd?:Boolean			== R has GcdDomain;
	local denom(B:MQ, r:I):R		== denom row(B, r);

	makeRowIntegral(B:MQ, r:I):(R, V R) == {
		import from VectorOverQuotient(R, Q);
		makeIntegral row(B, r);
	}

	makeColIntegral(B:MQ, c:I):(R, V R) == {
		import from VectorOverQuotient(R, Q);
		makeIntegral column(B, c);
	}

	-- Most of those functions use the fact that IntegralDomain's are
        -- commutative (if quotients of noncommutative domains are used
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

	if Q has QuotientFieldCategory0 R then {
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
	local denom(v:V Q):R == {
		import from I, Q, List R;
		denoms := [denominator(v.i) for i in 1..#v];
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

	local makeRowIntegral!(B:MQ, r:I, A:MR):() == {
		import from I, Q;
		c := cols B;
		ASSERT(c <= cols A); ASSERT(r <= rows A); ASSERT(r > 0);
		d := denom(B, r);
		for j in 1..c repeat A(r, j) := numerator(d * B(r, j));
	}

	makeRowIntegral(B:MQ):MR == {
		import from I, V R;
		(r, c) := dimensions B;
		A:MR := zero(r, c);
		for i in 1..r repeat makeRowIntegral!(B, i, A);
		A;
	}
}
