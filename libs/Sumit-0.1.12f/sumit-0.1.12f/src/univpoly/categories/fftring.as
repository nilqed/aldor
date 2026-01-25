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
----------------------------- fftring.as ----------------------------------
#include "sumit"

#if ASDOC
\thistype{FFTRing}
\History{Manuel Bronstein}{29/7/98}{created}
\Usage{\this: Category}
\Descr{\this~is the category of rings that export an algorithm for
the FFT product of univariate polynomials over themselves.}
\begin{exports}
\category{CommutativeRing}\\
fft: &
(P:POL \%) $\to$ (P, P) $\to$ Partial P & FFT product\\
fft!: & (P:POL \%) $\to$ (P, P, P) $\to$ Boolean & FFT product\\
fftCutoff: & $\to$ SingleInteger & Cutoff for FFT in $R[x]$\\
\end{exports}
\begin{aswhere}
POL &==& UnivariatePolynomialCategory0\\
\end{aswhere}
#endif

FFTRing: Category == CommutativeRing with {
	fft: (P: UnivariatePolynomialCategory0 %) -> (P, P) -> Partial P;
#if ASDOC
\aspage{fft}
\Usage{ \name(P)(p,q) }
\Signature{(P: UnivariatePolynomialCategory0 \%)}{(P, P) $\to$ Partial P}
\Params{
{\em P} & UnivariatePolynomialCategory0 \% & A polynomial type\\
{\em p,q} & P & Polynomials\\
}
\Retval{Returns the product $pq$ computed using FFT.}
\seealso{fft!(\this)}
#endif
	fft!: (P: UnivariatePolynomialCategory0 %) -> (P, P, P) -> Boolean;
#if ASDOC
\aspage{fft!}
\Usage{ \name(P)(r,p,q) }
\Signature{(P: UnivariatePolynomialCategory0 \%)}{(P, P, P) $\to$ Boolean}
\Params{
{\em P} & UnivariatePolynomialCategory0 \% & A polynomial type\\
{\em r,p,q} & P & Polynomials\\
}
\Retval{Replaces $r$ by $r + pq$ where the product is computed using FFT.
The space occupied by the first argument $r$ is allowed to be reused.
Returns \true~if the product could not be computed by the FFT method,
\false~otherwise.
}
\seealso{fft(\this)}
#endif
	fftCutoff: SingleInteger;
#if ASDOC
\aspage{fftCutoff}
\Usage{\name}
\Signature{}{SingleInteger}
\Retval{Returns $n$ such that the FFT multiplication is used
in $R[x]$ for polynomials of degree greater than or equal to $n$.}
\Remarks{If this constant is $0$, then FFT multiplication is
not used at all in $R[x]$.}
#endif
}

