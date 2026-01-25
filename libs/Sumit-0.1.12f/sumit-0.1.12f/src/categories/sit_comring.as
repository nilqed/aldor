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
------------------------------ sit_comring.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{CommutativeRing}
\History{Manuel Bronstein}{22/11/94}{created}
\History{Manuel Bronstein}{24/09/96}{added exactFactors}
\History{Manuel Bronstein}{6/12/96}{added karatsubaCutoff}
\Usage{\this: Category}
\Descr{\this~is the category of commutative rings.}
\begin{exports}
\category{\astype{Ring}}\\
\asexp{canonicalUnitNormal?}: & $\to$ \astype{Boolean} &
Check if \asexp{unitNormal} is canonical\\
\asexp{divideBy}: & \% $\to$ (\% $\to$ \%) & division procedure\\
\asexp{divDiffProd}: & (\%, \%, \%, \%, \%) $\to$ \% &
Combined product and quotient\\
\asexp{divSumProd}: & (\%, \%, \%, \%, \%, \%, \%) $\to$ \% &
Combined product and quotient\\
\asexp{exactQuotient}: & (\%, \%) $\to$ \astype{Partial} \% & Exact quotient\\
\asexp{karatsubaCutoff}: & $\to$ \astype{MachineInteger} &
Cutoff for Karatsuba in $R[x]$\\
\asexp{quotient}: & (\%, \%) $\to$ \% & Exact quotient\\
\asexp{reciprocal}: & \% $\to$ \astype{Partial} \% & Inverse\\
\asexp{unitNormal}:
& \% $\to$ (\%,\%,\%) & Representative of the associates\\
& (\%, \%) $\to$ (\%,\%) & \\
\asexp{unit?}: & \% $\to$ \astype{Boolean} & Test whether an element is a unit\\
\end{exports}
#endif

define CommutativeRing: Category == Ring with {
	canonicalUnitNormal?: Boolean;
#if ALDOC
\aspage{canonicalUnitNormal}
\Usage{\name}
\Signature{}{\astype{Boolean}}
\Retval{Returns \true~if {\tt unitNormal} is canonical in the following sense:
if $x = v x'$ for some unit $v$ and ${\tt unitNormal}(x)$ returns
$(u, y, u^{-1})$ and ${\tt unitNormal}(x')$ returns $(u', y', u'{}^{-1})$,
then $y = y'$.}
\seealso{\asexp{unitNormal}, \asexp{unit?}}
#endif
	divideBy: % -> (% -> %);
#if ALDOC
\aspage{divideBy}
\Usage{\name~x}
\Signature{\%}{\% $\to$ \%}
\Params{ {\em x} & \% & An element of the ring\\ }
\Retval{Returns a procedure p which performs exact division by $x$.
p should only be called when a division is exact.}
#endif
	divDiffProd: (%,%,%,%,%) -> %;
#if ALDOC
\aspage{divDiffProd}
\Usage{\name(a1, a2, b1, b2, q)}
\Signature{(\%, \%, \%, \%, \%)}{\%}
\Params{{\em a1, a2, b1, b2, q} & \% & Elements of the ring}
\Retval{\name(a1, a2, b1, b2, q) returns $(a1\,a2 - b1\,b2)/q$.}
#endif
	divSumProd: (%,%,%,%,%,%,%) -> %;
#if ALDOC
\aspage{divSumProd}
\Usage{\name(a1, a2, b1, b2, c1, c2, q)}
\Signature{(\%, \%, \%, \%, \%, \%, \%)}{\%}
\Params{{\em a1, a2, b1, b2, c1, c2, q} & \% & Elements of the ring}
\Retval{
\name(a1, a2, b1, b2, c1, c2, q) returns $(a1\,a2 + b1\,b2 + c1\,c2)/q$.
}
#endif
	exactQuotient: (%, %) -> Partial %;
#if ALDOC
\aspage{exactQuotient}
\Usage{\name(x, y)}
\Signature{(\%, \%)}{\astype{Partial} \%}
\Params{
{\em x} & \% & The numerator\\
{\em y} & \% & The denominator\\
}
\Retval{Returns $q$ such that $x = q\, y$ if such a $q$ exists,
\failed otherwise.}
\seealso{\asexp{quotient}}
#endif
	karatsubaCutoff: MachineInteger;
#if ALDOC
\aspage{karatsubaCutoff}
\Usage{\name}
\Signature{}{\astype{MachineInteger}}
\Retval{Returns $n$ such that the Karatsuba multiplication is used
in $R[x]$ for polynomials of degree greater than or equal to $n$.}
\Remarks{If this constant is $0$, then Karatsuba multiplication is
not used at all in $R[x]$. The default value is always $0$ so you only
need to define another value if you want Karatsuba to be used in $R[x]$.}
#endif
	quotient: (%, %) -> %;
#if ALDOC
\aspage{quotient}
\Usage{\name(x, y)}
\Signature{(\%, \%)}{\%}
\Params{
{\em x} & \% & The numerator\\
{\em y} & \% & The denominator\\
}
\Retval{Returns $q$ such that $x = q\, y$ if such a $q$ exists.}
\Remarks{Use this function only when it is guaranteed that y divides x
exactly. If there is a nonzero remainder, this function may produce a wrong
quotient instead of an error, so use the exactQuotient function when
there is the possibility of a nonzero remainder. When however y is known
to divide x exactly, then quotient can have better efficiency than the other
divisions.}
\seealso{\asexp{exactQuotient}}
#endif
	reciprocal: % -> Partial %;
#if ALDOC
\aspage{reciprocal}
\Usage{\name~x}
\Signature{\%}{\astype{Partial} \%}
\Params{ {\em x} & \% & An element of the ring\\ }
\Retval{Returns $y$ such that $x\, y = 1$ if such a $y$ exists,
\failed otherwise.}
#endif
	unitNormal: % -> (%, %, %);
	-- TEMPORARY: CANNOT OVERLOAD (BUG 1272)
	-- unitNormal: (%, %) -> (%, %);
	unitNormalize: (%, %) -> (%, %);
#if ALDOC
\aspage{unitNormal}
\Usage{(y, u, u1) := \name x\\ (y, z1) := \name(x, z)}
\Signatures{
\name: \% $\to$ (\%, \%. \%)\\
\name: (\%,\%) $\to$ (\%. \%)\\
}
\Params{ {\em x,y} & \% & Elements of the ring\\ }
\Retval{ \name(x) returns $(y, u, u^{-1})$, while
\name(x,z) returns $(y, u^{-1} z)$. In both cases, $x = u y$ and
$u$ is a unit.}
\seealso{\asexp{canonicalUnitNormal?}, \asexp{unit?}}
#endif
	unit?: % -> Boolean;
#if ALDOC
\aspage{unit?}
\Usage{\name~x}
\Signature{\%}{\astype{Boolean}}
\Params{ {\em x} & \% & An element of the ring\\ }
\Retval{ Returns \true~if $x$ is a unit, \ie $x \, y = 1$ for some $y$,
\false~otherwise.}
\seealso{\asexp{canonicalUnitNormal?}, \asexp{unitNormal}}
#endif
	default {
		karatsubaCutoff:MachineInteger	== 0;
		canonicalUnitNormal?:Boolean	== false;
		unitNormal(x:%):(%, %, %)	== (x, 1, 1);
		reciprocal(x:%):Partial(%) 	== exactQuotient(1, x);

		(a:%)^(n:Integer):% == {
			import from BinaryPowering(%, Integer);
			binaryExponentiation(a, n);
		}

		-- TEMPORARY: CANNOT OVERLOAD (BUG 1272)
		-- unitNormal(x:%, z:%):(%, %) == {
		unitNormalize(x:%, z:%):(%, %) == {
			(y, u, uinv) := unitNormal x;	-- x = u y
			(y, uinv * z);
		}

		divideBy(l:%):(%->%) == {
			import from Partial %;
			one? l => (a:%):% +-> a;
			failed?(u := reciprocal l) => (a:%):% +-> quotient(a,l);
			retru := retract u;
			(a:%):% +-> retru * a;
		}

		quotient(x:%, y:%):% == {
			import from Partial %;
			retract exactQuotient(x, y);
		}

		unit?(x:%):Boolean == {
			import from Partial %;
			~(zero? x or failed? reciprocal x)
		}

		divDiffProd(a1:%, a2:%, b1:%, b2:%, q:%):% ==
			quotient(a1 * a2 - b1 * b2, q);

		divSumProd(a1:%, a2:%, b1:%, b2:%, c1:%, c2:%, q:%):% ==
			quotient(a1 * a2 + b1 * b2 + c1 * c2, q);
	}
}
