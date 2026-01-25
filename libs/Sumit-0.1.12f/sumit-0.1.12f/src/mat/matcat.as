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
------------------------   matcat.as   -----------------------
#include "sumit"

#if ASDOC
\thistype{MatrixCategory}
\History {Marco Codutti}{12 may 95}{created}
\Usage   {\this~R: Category}
\Params  { {\em R} & SumitRing & The domain of the coefficients\\ }
\Descr   {\this~is a category for matrices with coefficients in an arbitrary 
	     SumitRing R.}
\begin{exports}
\category{MatrixCategory0 R}\\
\end{exports}
#endif

macro {
	I   == SingleInteger;
	ARR == PrimitiveArray;
	LA  == LinearAlgebra;
	RID == R pretend IntegralDomain;
	RF  == R pretend SumitField;
	RSPF == R pretend SmallPrimeFieldCategory0;
	SPF == SmallPrimeFieldGaussElimination(RSPF, %);
	OGE == OrdinaryGaussElimination(RF, %);
	TWO == TwoStepFractionFreeGaussElimination(RID, %);
}

MatrixCategory(R:SumitRing): Category == MatrixCategory0(R) with {
	if R has IntegralDomain then {
		default {
		local field?:Boolean	== R has SumitField;
		local laring?:Boolean	== R has LinearAlgebraRing;
		local spf?:Boolean	== R has SmallPrimeFieldCategory0;

		determinant(a:%):R == {
			laring? => ladet a;
			spf? => determinant(a)$LA(RID, %, SPF);
			field? => determinant(a)$LA(RID, %, OGE);
			determinant(a)$LA(RID, %, TWO);
		}

		rank(a:%):I == {
			laring? => larank a;
			spf? => rank(a)$LA(RID, %, SPF);
			field? => rank(a)$LA(RID, %, OGE);
			rank(a)$LA(RID, %, TWO);
		}

		span(a:%):(I, ARR I) == {
			laring? => laspan a;
			spf? => span(a)$LA(RID, %, SPF);
			field? => span(a)$LA(RID, %, OGE);
			span(a)$LA(RID, %, TWO);
		}

		nullSpace(a:%):List Vector R == {
			laring? => lanullspace a;
			spf? => nullspace(a)$LA(RID, %, SPF);
			field? => nullspace(a)$LA(RID, %, OGE);
			nullspace(a)$LA(RID, %, TWO);
		}

		if R has LinearAlgebraRing then {
			local ladet(a:%):R == {
				import from R;
				determinant(%)(a);
			}

			local laspan(a:%):(I, ARR I) == {
				import from R;
				span(%)(a);
			}

			local larank(a:%):I == {
				import from R;
				rank(%)(a);
			}

			local lanullspace(a:%):List Vector R == {
				import from R;
				nullSpace(%)(a);
			}
		}
		}
	}
}
