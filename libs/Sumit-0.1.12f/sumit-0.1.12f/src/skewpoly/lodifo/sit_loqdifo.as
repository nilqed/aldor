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
------------------------------ sit_lodqifo.as ------------------------------
-- Copyright (c) Manuel Bronstein 1999
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

macro {
	Z  == Integer;
	Rx == Fraction RX;
}

#if ALDOC
\thistype{LinearOrdinaryQDifferenceOperator}
\History{Manuel Bronstein}{13/12/99}{created}
\Usage{
import from \this(R, q, Rx);\\
import from \this(R, q, Rx, Q);\\
}
\Params{
{\em R} & \astype{Ring} & A ring\\
{\em q} & R & An element of R to use for the action\\
{\em Rx} & \astype{UnivariatePolynomialCategory} R & A polynomial ring over R\\
{\em Q} & \astype{Symbol} & The variable name (optional)\\
}
\Descr{\this(R, q, Rx, Q) implements linear ordinary $q$--difference
	operators with coefficients in Rx and shift $p(x) \to p(q x)$.}
\begin{exports}
\category{\astype{LinearOrdinaryDifferenceOperatorCategory} Rx}\\
\end{exports}
#endif

LinearOrdinaryQDifferenceOperator(R:Ring, q:R,
	RX:UnivariatePolynomialCategory R,
	avar:Symbol == new()): LinearOrdinaryDifferenceOperatorCategory RX == {
		import from R, Automorphism RX;

		local sigma(p:RX, n:Z):RX == {
			zero? n => p;
			p monomial(q^n, 1);
		}

		local msigma: Automorphism RX == morphism sigma;
		LinearOrdinaryDifferenceOperator(RX, msigma, avar) add {
			shift:Automorphism RX == msigma;
		}
}

#if ALDOC
\thistype{LinearOrdinaryQDifferenceOperatorQ}
\History{Manuel Bronstein}{30/11/2000}{created}
\Usage{
import from \this(R, q, Rx);\\
import from \this(R, q, Rx, Q);\\
}
\Params{
{\em R} & \astype{GcdDomain} & A ring\\
{\em q} & R & An element of R to use for the action\\
{\em Rx} & \astype{UnivariatePolynomialCategory} R & A polynomial ring over R\\
{\em Q} & \astype{Symbol} & The variable name (optional)\\
}
\Descr{\this(R, q, Rx, Q) implements linear ordinary $q$--difference
	operators with coefficients in the fraction field of Rx
	and shift $p(x) \to p(q x)$.}
\begin{exports}
\category{
\astype{LinearOrdinaryDifferenceOperatorCategory} \astype{Fraction} Rx}\\
\end{exports}
#endif

LinearOrdinaryQDifferenceOperatorQ(R:GcdDomain, q:R,
	RX:UnivariatePolynomialCategory R, avar:Symbol == new()):
		LinearOrdinaryDifferenceOperatorCategory Rx == {
		import from R, Automorphism Rx;

		local sigma(p:Rx, n:Z):Rx == {
			import from RX;
			zero? n => p;
			qnx := monomial(q^n, 1);
			numerator(p)(qnx) / denominator(p)(qnx);
		}

		local msigma: Automorphism Rx == morphism sigma;
		LinearOrdinaryDifferenceOperator(Rx, msigma, avar) add {
			shift:Automorphism Rx == msigma;
		}
}

