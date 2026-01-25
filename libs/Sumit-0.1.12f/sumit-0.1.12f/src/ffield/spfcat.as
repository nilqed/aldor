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
----------------------------- spfcat.as ----------------------------------
#include "sumit"

#if ASDOC
\thistype{SmallPrimeFieldCategory}
\History{Manuel Bronstein}{24/7/98}{created}
\Usage{\this: Category}
\Descr{\this~is the category for prime fields of the form
$\ZZ / p \ZZ$, for which p is a machine prime.}
\begin{exports}
\category{FFTRing}\\
\category{PrimeFieldCategory}\\
\category{SmallPrimeFieldCategory0}\\
\category{UnivariateGcdRing}\\
\end{exports}
#endif

macro {
	I == SingleInteger;
	Z == Integer;
	POLY == UnivariatePolynomialCategory0;
	A == PrimitiveArray;
}

SmallPrimeFieldCategory: Category ==
	Join(PrimeFieldCategory, SmallPrimeFieldCategory0,
		UnivariateGcdRing, FFTRing) with {
		default {
			fftCutoff:I	== 0;
			local charac:Z	== characteristic$%;
			-- TEMPORARY: TERRIBLE 1.1.11e COMPILER BUG
			-- local schar:I	== retract charac;
			biglift(a:%):Z	== lift(a)::Z;
			coerce(a:Z):%	== reduce retract(a mod charac);

			local makeArray(P:POLY %):(P, I) -> A I == {
				import from Z;
				(p:P, d:I):A I +-> {
					a := new(d1 := next d, 0);
					for term in p repeat {
						(c, e) := term;
						a(d1 - retract e) := lift c;
					}
					a;
				}
			}

			fft!(P:POLY %):(P, P, P) -> Boolean == {
				import from DiscreteFFT %;
				fftTimes! P;
			}

			fft(P:POLY %):(P, P) -> Partial P == {
				import from DiscreteFFT %;
				fftTimes P;
			}

			gcdUP(P:POLY %):(P,P) -> P == {
				import from I, A I, Z, ModulopUnivariateGcd;
				array := makeArray P;
				norm := monic$P;
				-- TEMPORARY: TERRIBLE 1.1.11e COMPILER BUG
				schar:I := retract charac;
				(log, exp, log?) := discreteLogTable();
				(p:P, q:P):P +-> {
					zero? p => norm q;
					zero? q => norm p;
					zero?(dp := degree p)
						or zero?(dq := degree q) => 1;
					if dp < dq then {	-- swap p,q
						ap := array(q,ep := retract dq);
						aq := array(p,eq := retract dp);
					}
					else {
						ap := array(p,ep := retract dp);
						aq := array(q,eq := retract dq);
					}
					ASSERT(ep >= eq);
					(v, d, s) := {
						log? => gcd!(ap, ep, aq, eq, 1,_
								schar,log,exp);
						gcd!(ap, ep, aq, eq, 1, schar);
					}
					-- monic gcd is now in v(s),v(s+1),...
					g:P := 0;
					for i in 0..d repeat
						g := add!(g,v(s+i)::%,(d-i)::Z);
					g;
				}
			}

			gcdquoUP(P:POLY %):(P,P) -> (P, P, P) == {
				pgcd := gcdUP P;
				(p:P, q:P):(P, P, P) +-> {
					g := pgcd(p, q);
					(g, quotient(p, g), quotient(q, g));
				}
			}
		}
}
