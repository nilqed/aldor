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
------------------------------ dplace.as --------------------
#include "sumit"

macro Z == Integer;

#if ASDOC
\thistype{DifferentialPlace}
\History{Manuel Bronstein}{23/5/95}{created}
\Usage{\this(R, F): Category}
\Params{
{\em R} & Ring & The coefficient ring of the place\\
{\em F} & SumitRing & The residue ring at the place\\
}
\Descr{\this(R, F) is the category of places over R which allow derivations.}
\begin{exports}
\category{Place(R, F)}\\
normal?: & Derivation R $\to$ Boolean & Check whether a derivation is normal\\
orderDrop: & Derivation R $\to$ Integer & Order drop of a derivation\\
residue: & Derivation R $\to$ F & Residue of a derivation\\
\end{exports}
#endif

DifferentialPlace(R:Ring, Residue:SumitRing):Category == Place(R,Residue) with {
	normal?: Derivation R -> Boolean;
#if ASDOC
\aspage{normal?}
\Usage{\name~D}
\Signature{Derivation R}{Boolean}
\Params{ {\em D} & Derivation R & A derivation on R\\ }
\Retval{Returns \true~if the derivation D is normal at the place,
\false~otherwise.}
#endif
	orderDrop: Derivation R -> Z;
#if ASDOC
\aspage{orderDrop}
\Usage{\name~D}
\Signature{Derivation R}{Integer}
\Params{ {\em D} & Derivation R & A derivation on R\\ }
\Retval{Returns $\nu(D f) - \nu(f)$ for any $f \in R$ with $\nu(f) \ne 0$.}
\Remarks{This function requires that the function $f \to \nu(D f) - \nu(f)$
is constant over the elements of $R$ with nonzero order. This fact is not
checked by this function.}
\seealso{residue(\this)}
#endif
	residue: Derivation R -> Residue;
#if ASDOC
\aspage{residue}
\Usage{\name~D}
\Signature{Derivation R}{F}
\Params{ {\em D} & Derivation R & A derivation on R\\ }
\Retval{Returns $\text{leadingCoefficient}(D(f)/f) / \nu(f)$ for any
$f \in R$ with $\nu(f) \ne 0$.}
\Remarks{This function requires that the function
$f \to \text{leadingCoefficient}(D(f)/f) / \nu(f)$
is constant over the elements of $R$ with nonzero order. This fact is not
checked by this function.}
\seealso{orderDrop(\this)}
#endif
}
