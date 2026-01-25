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
------------------------------ makepring.as ------------------------------
#include "sumit"

#if ASDOC
\thistype{MakePartialRing}
\History{Manuel Bronstein}{15/04/98}{created}
\Usage{import from \this(R, f)}
\Params{
R & SumitRing & A ring\\
f & R $\to$ Partial Integer & A retraction to the integers\\
}
\Descr{\this(R, f) is a partial ring isomorphic to R. The function $f$
is used to retract elements of this partial ring to integers whenever
possible. This type can be used in order to build an evaluator that
interprets expression trees into R.}
\begin{exports}
\category{PartialRing}\\
coerce: & R $\to$ \% & Convert an element of R to one of the partial ring\\
coerce: & \% $\to$ R & Convert an element of the partial ring to one of R\\
\end{exports}
#endif

MakePartialRing(R:SumitRing, int:R -> Partial Integer): PartialRing with {
	coerce: R -> %;
	coerce: % -> R;
} == add {
	macro Rep == R;
	import from Rep;

	local field?:Boolean		== R has Field;
	local comring?:Boolean		== R has CommutativeRing;
	0:%				== 0$R :: %;
	1:%				== 1$R :: %;
	coerce(n:Integer):%		== n::R::%;
	coerce(p:R):%			== per p;
	coerce(a:%):R			== rep a;
	- (b:%):Partial %		== [(-(b::R))::%];
	(a:%) + (b:%):Partial %		== [(a::R + b::R)::%];
	(a:%) - (b:%):Partial %		== [(a::R - b::R)::%];
	(a:%) * (b:%):Partial %		== [(a::R * b::R)::%];
	(a:%) = (b:%):Boolean		== a::R = b::R;
	integer(a:%):Partial Integer	== int(a::R);
	extree(a:%):ExpressionTree	== extree(a::R);

	if R has Field then {
		local fdiv(a:%, b:%):Partial %	== [(a::R / b::R)::%];
	}

	if R has CommutativeRing then {
		local crdiv(a:%, b:%):Partial % == {
			import from Partial R;
			failed?(u := exactQuotient(a::R, b::R)) => failed;
			[retract(u)::%];
		}
	}

	(a:%) / (b:%):Partial %	== {
		field? => fdiv(a, b);
		comring? => crdiv(a, b);
		one?(b::R) => [a];
		failed;
	}

	(a:%) ^ (b:%):Partial %	== {
		import from Partial Integer;
		failed?(u := integer b) => failed;
		[((a::R)^retract(u))::%];
	}
}
