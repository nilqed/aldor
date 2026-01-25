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
--------------------------- sit_sprfcat.as ------------------------------
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{SmallPrimeFieldCategory}
\History{Manuel Bronstein}{24/7/98}{created}
\Usage{\this: Category}
\Descr{\this~is the category for prime fields of the form $\ZZ / p \ZZ$
where $p \in \ZZ$ is a machine prime.}
\begin{exports}
% \category{\astype{FFTRing}}\\
\category{\astype{PrimeFieldCategory}}\\
\category{\astype{SmallPrimeFieldCategory0}}\\
\category{\astype{UnivariateGcdRing}}\\
\end{exports}
#endif

macro {
	Z	== MachineInteger;
	AZ	== Array Z;
	V	== Vector %;
	MAT	== MatrixCategory;
	POLY	== UnivariatePolynomialCategory0;
	GCD	== SmallPrimeFieldCategoryGcd;
	LINALG	== SmallPrimeFieldCategoryLinearAlgebra;
}

define SmallPrimeFieldCategory: Category ==
	Join(PrimeFieldCategory, SmallPrimeFieldCategory0,
		UnivariateGcdRing, LinearAlgebraRing) with {
		-- UnivariateGcdRing, LinearAlgebraRing, FFTRing) with {
	default {
		-- fftCutoff:Z	== 0;
#if WAITFORGOODFFT
		fft!(P:POLY %):(P, P, P) -> Boolean == {
			import from DiscreteFFT %;
			fftTimes! P;
		}

		fft(P:POLY %):(P, P) -> Partial P == {
			import from DiscreteFFT %;
			fftTimes P;
		}
#endif

		gcdUP(P:POLY %):(P,P) -> P		== gcdSPF$GCD(%, P);
		gcdquoUP(P:POLY %):(P,P) -> (P,P,P)	== gcdquoSPF$GCD(%, P);

		determinant(M:MAT %):M -> %	== determinant$LINALG(%, M);
		inverse(M:MAT %):M -> (M, V)	== inverse$LINALG(%, M);
		kernel(M:MAT %):M -> M		== kernel$LINALG(%, M);
		rank(M:MAT %):M -> Z		== rank$LINALG(%, M);
		solve(M:MAT %):(M,M) -> (M,M,V)	== solve$LINALG(%, M);
		span(M:MAT %):M -> AZ		== span$LINALG(%, M);

		linearDependence(g:Generator V, n:Z):V ==
			linearDependence(g, n)$LINALG(%, DenseMatrix %);

		particularSolution(M:MAT %):(M, M) -> (M, V) ==
			particularSolution$LINALG(%, M);

		maxInvertibleSubmatrix(M:MAT %):M -> (AZ, AZ) ==
			maxInvertibleSubmatrix$LINALG(%, M);
	}
}
