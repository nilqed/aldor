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
----------------------------- primtable.as ----------------------------------
#include "sumit"

macro Z	== SingleInteger;

PrimeTable: Category == with {
	primes: Array Z;
	fourier: Array Z;
	roots: Array Z
};


#if ASDOC
\thistype{PrimeCollection}
\History{Manuel Bronstein}{26/4/96}{created}
\Usage{\this: Category}
\Descr{\this~is the category of collections of primes with various
properties and various sizes.}
\begin{exports}
fourierPrime: & Z $\to$ (Z, Z) & Fourier prime\\
maxPrime: & $\to$ Z & Largest prime\\
nextPrime & Z $\to$ Z & First prime above a given number\\
previousPrime & Z $\to$ Z & First prime below a given number\\
randomPrime & () $\to$ Z & Random prime\\
\end{exports}
\Aswhere{
Z & == & SingleInteger\\
}
#endif

PrimeCollection: Category == with {
	fourierPrime: Z -> (Z, Z);
#if ASDOC
\aspage{fourierPrime}
\Usage{\name~n}
\Signature{SingleInteger}{(SingleInteger,SingleInteger)}
\Retval{Returns $(p,\omega)$ such that $p$ is a prime of the form
$p = 2^n k + 1$ with $k$ odd, and $\omega$ is a primitive $\sth{2^n}$
root of unity in $\mathbbm{F}_p$. Returns $(0,0)$ if $n$ is too large.}
#endif
	maxPrime: Z;
#if ASDOC
\aspage{maxPrime}
\Usage{\name}
\Signature{}{SingleInteger}
\Retval{Returns the largest prime in the collection.}
#endif
	nextPrime: Z -> Z;
#if ASDOC
\aspage{nextPrime}
\Usage{\name~n}
\Signature{SingleInteger}{SingleInteger}
\Params{ {\em n} & SingleInteger & An integer\\ }
\Retval{Returns the smallest prime $p$ in the collection with $n < p$,
$0$ if there are none.}
\seealso{previousPrime(\this), randomPrime(\this)}
#endif
	previousPrime: Z -> Z;
#if ASDOC
\aspage{previousPrime}
\Usage{\name~n}
\Signature{SingleInteger}{SingleInteger}
\Params{ {\em n} & SingleInteger & An integer\\ }
\Retval{Returns the largest prime $p$ in the collection with $n > p$,
$0$ if there are none.}
\seealso{nextPrime(\this), randomPrime(\this)}
#endif
	randomPrime: () -> Z;
#if ASDOC
\aspage{randomPrime}
\Usage{\name()}
\Signature{()}{SingleInteger}
\Retval{Returns a random prime in the collection.}
\seealso{nextPrime(\this), previousPrime(\this)}
#endif
};
