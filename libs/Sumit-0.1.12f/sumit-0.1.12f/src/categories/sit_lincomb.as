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
-------------------------- sit_lincomb.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1997
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1997
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{LinearCombinationType}
\History{Manuel Bronstein}{17/2/97}{created}
\Usage{\this~R:Category}
\Params{
{\em R} & \astype{SumitType} & The coefficient domain\\
        & \astype{AdditiveType} &\\
}
\Descr{\this~R is the category of types containing linear
combinations of their elements with coefficients in R.}
\Remarks{Use \astype{Module} instead
if R is always meant to be a \astype{Ring}.}
\begin{exports}
\category{\astype{AdditiveType}}\\
\category{\astype{SumitType}}\\
\asexp{$*$}: & (R, \%) $\to$ \% & Left-multiplication by a scalar\\
\asexp{add!}: & (\%, R, \%) $\to$ \% & In--place product and sum\\
\asexp{times!}: & (R, \%) $\to$ \% & In--place product by a scalar\\
\end{exports}
#endif

define LinearCombinationType(R:Join(AdditiveType, SumitType)):
	Category == Join(AdditiveType, SumitType) with {
		*: (R, %) -> %;
#if ALDOC
\aspage{$*$}
\Usage{r \name~p}
\Signature{(R, \%)}{\%}
\Params{
{\em r} & R & A scalar\\
{\em p} & \% & An element of the type\\
}
\Retval{Returns the product $r p$.}
\seealso{\asexp{times!}}
#endif
		add!: (%, R, %) -> %;
#if ALDOC
\aspage{add!}
\Usage{\name(p, r, q)}
\Signature{(\%, R, \%)}{\%}
\Params{
{\em p} & \% & An element of the type (to be destroyed)\\
{\em r} & R & A scalar\\
{\em q} & \% & An element of the type\\
}
\Retval{\name(p, r, q) returns $p + r q$.}
\Remarks{
The storage used by p is allowed
to be destroyed or reused, so p is lost after this call.
This function may cause p to be destroyed, so do not use it unless
p has been locally allocated, and is guaranteed not to share space
with other elements. Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
\seealso{\asexp{times!}}
#endif
		times!: (R, %) -> %;
#if ALDOC
\aspage{times!}
\Usage{\name(r, p)}
\Signature{(R, \%)}{\%}
\Params{
{\em r} & R & A scalar to be multiplied by p\\
{\em p} & \% & An element of the type (to be destroyed)\\
}
\Retval{Returns the product $r p$.}
\Remarks{The storage used by p is allowed to be destroyed or reused, so p
is lost after this call.
This may cause p to be destroyed, so do not use this unless
p has been locally allocated, and is thus guaranteed not to share space
with other elements. Some functions are
not necessarily copying their arguments and can thus create memory aliases.}
\seealso{\asexp{$\ast$},\asexp{add!}}
#endif
	default {
		add!(p:%, c:R, q:%):%	== add!(p, c * q);
		times!(c:R, p:%):%	== c * p;

		if R has Ring then {
			(n:Integer) * (p:%):% == { import from R; n::R * p; }
		}
	}
}
