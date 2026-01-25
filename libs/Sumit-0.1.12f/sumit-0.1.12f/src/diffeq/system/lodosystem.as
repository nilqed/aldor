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
------------------------------ lodosystem.as ------------------------------
#include "sumit"

macro {
	I == SingleInteger;
	Z == Integer;
	M == DenseMatrix;
	V == Vector;
}

#if ASDOC
\thistype{LinearOrdinaryDifferentialSystem}
\History{Manuel Bronstein}{6/5/97}{created}
\Usage{ import from \this~R}
\Params{
{\em R} & CommutativeRing & The coefficient ring of the operators\\
}
\Descr{\this~R provides linear ordinary differential
systems of first order with coefficients in R.}
\begin{exports}
adjoint: & \% $\to$ \% & Adjoint system\\
endomorphisms: & \% $\to$ \% & System for the endomorphisms ring\\
matrix: & \% $\to$ (R, DenseMatrix R) & Matrix representation\\
order: & \% $\to$ Integer & Number of unknowns\\
system: & (R, DenseMatrix R) $\to$ \% & Create a system\\
\end{exports}
\begin{exports}[if R has Join(Field, FiniteCharacteristic) then]
pCurvature: & (\%, Derivation R) $\to$ DenseMatrix R & p-Curvature\\
\end{exports}
#endif

LinearOrdinaryDifferentialSystem(R:CommutativeRing): with {
	adjoint: % -> %;
#if ASDOC
\aspage{adjoint}
\Usage{\name~L}
\Signature{\%}{\%}
\Params{ {\em L} & \% & A differential system\\ }
\Retval{Returns $L^\ast: a Y' = -A^T Y$ where $L$ is $a Y' = A Y$.}
#endif
	eigenTensor: % -> %;
#if ASDOC
\aspage{eigenTensor}
\Usage{\name~L}
\Signature{\%}{\%}
\Params{ {\em L} & \% & A differential system\\ }
\Retval{Returns the system
$$
{\cal E}(L): a Y' = \paren{I \otimes A - A^T \otimes I} Y
$$
where $L$ is $a Y' = A Y$.}
#endif
	matrix: % -> (R, M R);
#if ASDOC
\aspage{matrix}
\Usage{\name~L}
\Signature{\%}{(R, DenseMatrix R)}
\Params{ {\em L} & \% & A differential system\\ }
\Retval{Returns $(a, A)$ such that $L$ is the system $a Y' = A Y$.}
#endif
	order: % -> Z;
#if ASDOC
\aspage{order}
\Usage{\name~L}
\Signature{\%}{Integer}
\Params{ {\em L} & \% & A differential system\\ }
\Retval{Returns the number of unknowns of $L$.}
#endif
	if R has Join(Field, FiniteCharacteristic) then {
		pCurvature: (%, Derivation R) -> M R;
#if ASDOC
\aspage{pCurvature}
\Usage{\name(L,D)}
\Signature{(\%, Derivation R)}{DenseMatrix R}
\Params{
{\em L} & \% & A differential system\\
{\em D} & Derivation R & A derivation on R\\
}
\Retval{Returns $A_p$ in the sequence $A_1 = - A$,
$A_{k+1} = A_1 A_k + D A_k$, where $L$ is the system
$D Y = A Y$.}
#endif
}
	system: (R, M R) -> %;
#if ASDOC
\aspage{system}
\Usage{\name(a, A)}
\Params{
{\em a} & R & A coefficient\\
{\em A} & DenseMatrix R & A matrix\\
}
\Retval{Returns the differential system $a Y' = A Y$.}
#endif
} == add {
	macro Rep == Record(coeff:R, mat:M R);
	import from Rep;

	local coef(s:%):R	== rep(s).coeff;
	local mat(s:%):M R	== rep(s).mat;
	matrix(s:%):(R, M R)	== explode rep s;
	order(s:%):Z		== { import from Z, M R; rows(mat s)::Z }

	eigenTensor(s:%):% == {
		import from I, M R;
		A := mat s;
		id := one rows A;
		-- TEMPORARY: tensoring with id should not call general tensor
		system(coef s, substract!(tensor(id,A),tensor(transpose A,id)));
	}

	adjoint(s:%):% == {
		import from M R;
		system(coef s, minus! transpose mat s);
	}

	system(a:R, m:M R):% == {
		import from I;
		ASSERT(rows m = cols m);
		per [a, m];
	}

	sample:% == {
		import from I, R, M R;
		system(1, zero(1, 1));
	}

	if R has Join(Field, FiniteCharacteristic) then {
		pCurvature(s:%, D:Derivation R):M R == {
			import from Z, R;
			a1 := (- inv(coef s)) * mat s;
			ak := copy a1;
			f := function D;
			p := characteristic$R;
			for i in 2..p repeat {
				t := a1 * ak;
				ak := add!(map!(f, ak), t);
			}
			ak;
		}
	}
}
