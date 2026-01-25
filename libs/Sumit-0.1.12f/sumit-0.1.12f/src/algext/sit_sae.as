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
----------------------------- sit_sae.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1996
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1996-97
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{SimpleAlgebraicExtension}
\History{Manuel Bronstein}{27/12/96}{created}
\Usage{
import from \this(R, Rx, p)\\
import from \this(R, Rx, p, x)\\
}
\Params{
{\em R} & \astype{IntegralDomain} & The coefficient ring of the polynomials\\
{\em Rx} & \astype{UnivariatePolynomialCategory0} R & The type of the modulus\\
{\em p} & Rx & The modulus\\
{\em x} & \astype{Symbol} & The generator name (optional)\\
}
\Descr{\this(R, Rx, p) implements the algebraic extension $Rx / (p)$,
where $p$ is expected to be irreducible. It is possible to use this
type with reducible $p$, but then
divisions can throw the exception \astype{ReducibleModulusException}.
Use \astype{UnivariatePolynomialMod} if you want to prevent divisions
from being available.}
\begin{exports}
\category{\astype{SimpleAlgebraicExtensionCategory}(R, Rx)}\\
\end{exports}
#endif

macro UPMOD == UnivariatePolynomialMod(R, Rx, modulus, avar);

SimpleAlgebraicExtension(R:IntegralDomain, Rx: UnivariatePolynomialCategory0 R,
	modulus:Rx, avar:Symbol == new()):
		SimpleAlgebraicExtensionCategory(R, Rx) == UPMOD add {};


#if ALDOC
\thistype{SimpleAlgebraicExtensionCategory}
\History{Manuel Bronstein}{27/12/96}{created}
\Usage{ \this(R, Rx):Category }
\Params{
{\em R} & \astype{IntegralDomain} & The coefficient ring of the polynomials\\
{\em Rx} & \astype{UnivariatePolynomialCategory0} R & The type of the modulus\\
}
\Descr{\this(R, Rx) is the category of extensions of $R$ of the form
$Rx / (p)$ for some irreducible $p \in Rx$.
Use \astype{UnivariatePolynomialQuotient} for extensions where the
modulus is known to be reducible.}
\Remarks{It is possible to use this category with a reducible modulus, but then
divisions can throw the exception \astype{ReducibleModulusException}.}
\begin{exports}
\category{\astype{IntegralDomain}}\\
\category{\astype{UnivariatePolynomialQuotient}(R, Rx)}\\
\end{exports}
\begin{exports}[if R has \astype{Field} then]
\category{\astype{Field}}\\
\end{exports}
\begin{exports}[if R has \astype{FiniteField} then]
\category{\astype{FiniteField}}\\
\end{exports}
#endif

define SimpleAlgebraicExtensionCategory(R:IntegralDomain,
	Rx: UnivariatePolynomialCategory0 R): Category ==
		Join(IntegralDomain, UnivariatePolynomialQuotient(R, Rx)) with {
		if R has Field then Field;
		if R has FiniteField then FiniteField;
		default { if R has Field then {
			inv(f:%):% == {
				import from Partial %;
				failed?(u :=  reciprocal f) =>
					throw ReducibleModulusException(Rx,
						definingPolynomial, lift f);
				retract u;
			}
		} }
};

