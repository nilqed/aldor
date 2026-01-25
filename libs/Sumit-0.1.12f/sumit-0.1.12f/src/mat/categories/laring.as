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
----------------------------- laring.as ----------------------------------
-- Copyright Manuel Bronstein, 1998
-- Copyright INRIA, 1998

#include "sumit"

#if ASDOC
\thistype{LinearAlgebraRing}
\History{Manuel Bronstein}{27/4/98}{created}
\Usage{\this: Category}
\Descr{\this~is the category of rings that export an algorithm for
performing linear algebra for matrices over themselves.}
\begin{exports}
\category{IntegralDomain}\\
\category{RationalRootRing}\\
determinant: & (M:MatrixCategory0 \%) $\to$ M $\to$ \% & Determinant\\
nullSpace: &
(M:MatrixCategory0 \%) $\to$ M $\to$ List Vector \% & Basis of the nullspace\\
rank: & (M:MatrixCategory0 \%) $\to$ M $\to$ Z & Rank\\
span: & (M:MatrixCategory0 \%) $\to$ M $\to$ (Z, ARR Z) & Span\\
\end{exports}
\begin{aswhere}
Z &==& SingleInteger\\
ARR &==& PrimitiveArray\\
\end{aswhere}
#endif

macro {
	I == SingleInteger;
	ARR == PrimitiveArray;
}

LinearAlgebraRing: Category == IntegralDomain with {
	determinant: (M: MatrixCategory0 %) -> M -> %;
#if ASDOC
\aspage{determinant}
\Usage{ \name(M)(m) }
\Signature{(M: MatrixCategory0 \%)}{M $\to$ \%}
\Params{
{\em M} & MatrixCategory0 \% & A matrix type\\
{\em m} & M & A matrix\\
}
\Retval{Returns the determinant of m.}
#endif
	nullSpace: (M: MatrixCategory0 %) -> M -> List Vector %;
#if ASDOC
\aspage{nullSpace}
\Usage{ \name(M)(m) }
\Signature{(M: MatrixCategory0 \%)}{M $\to$ List Vector \%}
\Params{
{\em M} & MatrixCategory0 \% & A matrix type\\
{\em m} & M & A matrix\\
}
\Retval{Returns a basis for the nullspace of m.}
#endif
	rank: (M: MatrixCategory0 %) -> M -> I;
#if ASDOC
\aspage{rank}
\Usage{ \name(M)(m) }
\Signature{(M: MatrixCategory0 \%)}{M $\to$ SingleInteger}
\Params{
{\em M} & MatrixCategory0 \% & A matrix type\\
{\em m} & M & A matrix\\
}
\Retval{Returns the rank of m.}
#endif
	span: (M: MatrixCategory0 %) -> M -> (I, ARR I);
#if ASDOC
\aspage{span}
\Usage{\name(M)(m)}
\Signature{(M: MatrixCategory0 \%)}
{M $\to$ (SingleInteger, PrimitiveArray SingleInteger)}
\Params{
{\em M} & MatrixCategory0 \% & A matrix type\\
{\em m} & M & A matrix\\
}
\Retval{Returns $(r, [c_1,\dots,c_r])$ such that the columns
$c_1,\dots,c_r$ of $m$ form a basis of the span of $m$.}
#endif
}

