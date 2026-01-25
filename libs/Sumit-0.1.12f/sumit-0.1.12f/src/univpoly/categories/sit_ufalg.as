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
----------------------------- sit_ufalg.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"

macro Z == Integer;

#if ALDOC
\thistype{UnivariateFreeAlgebra}
\History{Manuel Bronstein}{22/5/95}{created}
\History{Thom Mulders}{27/5/97}{added partial add!}
\History{Manuel Bronstein}{14/4/2000}{allowed infinite dimensional algebras}
\Usage{\this~R: Category}
\Params{
{\em R} & \astype{SumitType} & The coefficient domain\\
        & \astype{ArithmeticType} &\\
}
\Descr{\this~is a common category for commutative and noncommutative
univariate polynomials and power series with coefficients in an arbitrary
arithmetic system R and with respect to an arbitrary basis $(P_n)_{n \ge 0}$.}
\begin{exports}
\category{\astype{LinearArithmeticType} R}\\
\asexp{add!}: & (\%, R, Z) $\to$ \% & In-place addition of a monomial\\
\asexp{add!}: & (\%, R, Z, \%) $\to$ \% & In-place product and sum\\
\asexp{apply}: & (\%, TREE) $\to$ TREE & Conversion to an expression tree\\
\asexp{apply}:
& (OUT, \%, \astype{Symbol}) $\to$ OUT & Write an element to a port\\
\asexp{coefficient}: & (\%, Z) $\to$ R & Extraction of a coefficient\\
\asexp{coefficients}:
& \% $\to$ \astype{Generator} R & Iterate over all the coefficients\\
\asexp{map}: & (R $\to$ R) $\to$ \% $\to$ \% & Lift a mapping\\
\asexp{map!}: & (R $\to$ R) $\to$ \% $\to$ \% & Lift a mapping\\
\asexp{monom}: & $\to$ \% & Term with degree 1 and coefficient 1\\
\asexp{monomial}: & (R, Z) $\to$ \% & Creation of a monomial\\
\asexp{setCoefficient!}: & (\%, Z, R) $\to$ \% &
In-place replacement of a coefficient\\
\asexp{shift}: & (\%, Z) $\to$ \% & Exponent translation\\
\asexp{shift!}: & (\%, Z) $\to$ \% & Exponent translation\\
\end{exports}
\begin{aswhere}
OUT &==& \astype{TextWriter}\\
TREE &==& \astype{ExpressionTree}\\
Z &==& \astype{Integer}\\
\end{aswhere}
#endif

define UnivariateFreeAlgebra(R:Join(ArithmeticType, SumitType)):
	Category == LinearArithmeticType R with {
	add!: (%, R, Z) -> %;
	add!: (%, R, Z, %) -> %;
#if ALDOC
\aspage{add!}
\Usage{\name(p, c, m)\\ \name(p, c, m, q)}
\Signatures{
\name: & (\%, R, \astype{Integer}) $\to$ \% \\
\name: & (\%, R, \astype{Integer}, \%) $\to$ \% \\
}
\Params{
{\em p} & \% & A polynomial or series (to be destroyed)\\
{\em c} & R & A scalar\\
{\em m} & \astype{Integer} & The degree of the monomial to add\\
{\em q} & \% &
A polynomial or series to be multiplied by $c P_m$ and added to p\\
}
\Retval{\name(p, c, m) computes the sum $p + c P_m$, while
\name(p, c, m, q) computes the sum $p + c P_m q$.
Note that $m$ is allowed to be negative in the second form but not
in the first.}
\Remarks{The storage used by p is allowed to be destroyed or reused, so p
is lost after this call. This may cause p to be destroyed, so do not use
this unless p has been locally allocated, and is thus guaranteed not to
share space with other polynomials. Some functions, like
\asfunc{UnivariateFreeFiniteAlgebra}{reductum} are
not necessarily copying their arguments and can thus create memory aliases.}
#endif
	apply: (%, ExpressionTree) -> ExpressionTree;
	apply: (TextWriter, %, Symbol) -> TextWriter;
#if ALDOC
\aspage{apply}
\Usage{\name(p, t)\\p~t\\ \name(port, p, x)\\ port(p, x)}
\Signatures{
\name: & (\%, \astype{ExpressionTree}) $\to$ \astype{ExpressionTree}\\
\name: & (\astype{TextWriter}, \%, \astype{Symbol}) $\to$ \astype{TextWriter}\\
}
\Params{
{\em p} & \% & A polynomial or series\\
{\em t} & \astype{ExpressionTree} & An expression tree\\
{\em x} & \astype{Symbol} & A name for the variables\\
{\em port} & \astype{TextWriter} & An output port\\
}
\Descr{\name(p, t) returns p as an expression tree,
using t as root variable name, while
\name(port, p, x) sends p to port using x as root variable name,
and returns the output port afterwards.}
\begin{asex}
\begin{ttyout}
import from Integer, DenseUnivariatePolynomial Integer;

p := monomial(1, 3) + monomial(2, 1) - monomial(1, 0);  -- p = x^3 + 2 x - 1
stdout(map((n:Integer):Integer +-> n + n)(p), -"x");
\end{ttyout}
writes
\begin{asoutput}
\> 2 x\^{}\{3\} + 4 x - 2
\end{asoutput}
to the standard stream {\tt stdout}.
\end{asex}
#endif
	coefficient: (%, Z) -> R;
#if ALDOC
\aspage{coefficient}
\Usage{\name(p, n)}
\Signature{(\%, \astype{Integer})}{R}
\Params{
{\em p} & \% & A polynomial or series\\
{\em n} & \astype{Integer} & An exponent\\
}
\Retval{Returns the coefficient of $p$ in $P_n$.}
#endif
	coefficients: % -> Generator R;
#if ALDOC
\aspage{coefficients}
\Usage{for c in \name~p repeat \{ \dots \} }
\Signature{\%}{\astype{Generator} R}
\Params{ {\em p} & \% & A polynomial or series\\ }
\Retval{Returns a generator that produces all the coefficients of $p$,
including the ones which are 0, sorted by increasing degree.}
\seealso{\asfunc{UnivariateFreeFiniteAlgebra}{generator},
\asfunc{UnivariateFreeFiniteAlgebra}{terms}}
#endif
	map: (R -> R) -> % -> %;
	map!: (R -> R) -> % -> %;
#if ALDOC
\aspage{map}
\astarget{\name!}
\Usage{\name~f\\\name!~f\\\name(f)(p)\\\name!(f)(p)}
\Signature{(R $\to$ R) $\to$ \%}{\%}
\Params{
{\em f} & R $\to$ R & A map\\
{\em p} & \% & A polynomial or series\\
}
\Descr{
\name(f)(p) returns
$$
f(p) = \sum_i f(a_i) P_i
$$
where $p = \sum_i a_i P_i$,
while \name(f) returns the mapping $p \to f(p)$. In both cases,
\name!~does not make a copy of $p$ but modifies it in place.}
#endif
	monom: %;
#if ALDOC
\aspage{monom}
\Usage{\name}
\Signature{}{\%}
\Retval{Returns $P_1$, \ie~the monomial with degree 1 and coefficient 1.}
\seealso{\asexp{monomial}}
#endif
	monomial: (R, Z) -> %;
#if ALDOC
\aspage{monomial}
\Usage{\name(c, n)}
\Signature{(R, \astype{Integer})}{\%}
\Params{
{\em c} & R & A scalar\\
{\em n} & \astype{Integer} & An exponent\\
}
\Retval{Returns the monomial $c P_n$.}
#endif
	setCoefficient!: (%, Z, R) -> %;
#if ALDOC
\aspage{setCoefficient!}
\Usage{\name(p, n, c)}
\Signature{(\%, \astype{Integer}, R)}{\%}
\Params{
{\em p} & \% & A polynomial or series\\
{\em n} & \astype{Integer} & An exponent\\
{\em c} & R & A coefficient\\
}
\Descr{Sets the coefficient of $P_n$ in $p$ to $c$,
and returns the modified $p$.}
\Remarks{The storage used by p is allowed to be destroyed or reused, so p
is lost after this call.
This may cause p to be destroyed, so do not use this unless
p has been locally allocated, and is thus guaranteed not to share space
with other polynomials. Some functions,
like \asfunc{UnivariateFreeFiniteAlgebra}{reductum} are
not necessarily copying their arguments and can thus create memory aliases.}
\seealso{\asexp{coefficient}}
#endif
	shift: (%, Z) -> %;
	shift!: (%, Z) -> %;
#if ALDOC
\aspage{shift}
\astarget{\name!}
\Usage{\name(p, m)\\ \name!(p, m)}
\Signature{(\%,\astype{Integer})}{\%}
\Params{
{\em p} & \% & A polynomial or series\\
{\em m} & \astype{Integer} & The amount to shift\\
}
\Retval{Returns
$$
\sum_{i \ge \max(0,-m)} a_i P_{i+m}
$$
where $p = \sum_{i \ge 0} a_i P_i$.}
\Remarks{When using \name!, the storage used by p is allowed to be
destroyed or reused, so p is lost after this call.
This may cause p to be destroyed, so do not use this unless
p has been locally allocated, and is thus guaranteed not to share space
with other polynomials.}
#endif
	default {
		add!(p:%, c:R, v:Z):%	== add!(p, monomial(c, v));
		coerce(c:R):%		== { import from Z; monomial(c, 0); }
		monom:%			== { import from R, Z; monomial(1, 1); }
		map!(f:R -> R)(p:%):%	== map(f) p;
		shift!(p:%, n:Z):%	== shift(p, n);

		apply(port:TextWriter, p:%, v:Symbol):TextWriter == {
			import from ExpressionTree;
			tex(port, p extree v);
		}

		(p:%) ^ (n:Z):% == {
			import from BinaryPowering(%, Z);
			assert(n >= 0);
			binaryExponentiation(p, n);
		}
	}
}
