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
-------------------------------- sit_eqccat.as ------------------------------
-- Copyright (c) Marco Codutti 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995
-----------------------------------------------------------------------------

#include "sumit"

macro TCR == (T pretend CommutativeRing);

#if ALDOC
\thistype{EqualityCondition}
\History {Marco Codutti}{14 June 95}{created}
\Usage   {\this~T: Category}
\Descr   {\this~T~is a category for equality and inequality
conditions on elements of T.}
\begin{exports}
\category{\astype{Condition}}\\
\asexp{=} : & (T,T) $\to$ \%  & assert that two objects are equal\\
\asexp{\~{}=}: & (T,T) $\to$ \%  & assert that two objects are different\\
\asexp{equalities}: & \% $\to$ \astype{Generator} \builtin{Cross}(T, T) &
iterate through the equalities\\
\asexp{inequalities}: & \% $\to$ \astype{Generator} \builtin{Cross}(T, T) &
iterate through the inequalities\\
\end{exports}
\begin{exports}[if R has \astype{CommutativeRing} then]
\asexp{nonzero}: & \% $\to$ \astype{Generator} T & inequalities (to $0$)\\
\asexp{split}: & (\%, T) $\to$ (\%, \%) & split on whether $a=0$ or $a\ne 0$\\
\asexp{zero}: & \% $\to$ \astype{Generator} T & equalities (to $0$)\\
\end{exports}
#endif

define EqualityCondition(T:SumitType): Category == Condition with {
	=: (T, T) -> %;
	~=: (T, T) -> %;
#if ALDOC
\aspage{=,\~{}=}
\astarget{=}
\astarget{\~{}=}
\Usage{a=b\\ a\~{}= b}
\Signature{(T,T)}{\%}
\Params{{\em a,b} & T & elements of T\\ }
\Retval{Return a condition that stipulates that $a=b$ (resp.~$a \ne b$)}
#endif
	equalities: % -> Generator Cross(T, T);
	inequalities: % -> Generator Cross(T, T);
#if ALDOC
\aspage{equalities,inequalities}
\astarget{equalities}
\astarget{inequalities}
\Usage{equalities~c\\inequalities~c}
\Signature{\%}{\astype{Generator} \builtin{Cross}(T, T)}
\Params{{\em c} & \% & a condition\\ }
\Retval{Return a generator that iterates through pairs $(a,b)$
such that $a = b$ (resp.~$a \ne b$) is part of $c$.}
\seealso{\asexp{nonzero},\asexp{zero}}
#endif
	if T has CommutativeRing then {
		nonzero: % -> Generator T;
		zero: % -> Generator T;
#if ALDOC
\aspage{zero,nonzero}
\astarget{nonzero}
\astarget{zero}
\Usage{zero~c\\ nonzero~c}
\Signature{\%}{\astype{Generator} T}
\Params{{\em c} & \% & a condition\\ }
\Retval{Return a generator that iterates through $a$'s such that
$a = 0$ (resp.~$a \ne 0$) is part of $c$.}
\seealso{\asexp{equalities},\asexp{inequalities}}
#endif
		split: (%, T) -> (%, %);
#if ALDOC
\aspage{split}
\Usage{\name(c, a)}
\Signature{(\%,T)}{(\%,\%)}
\Params{
{\em c} & \% & a condition\\
{\em a} & T & an element of T\\
}
\Retval{Return $(c /\backslash a = 0, c /\backslash a\ne 0)$.}
#endif
	}
	default {
		if T has CommutativeRing then {
			split(c:%, a:T):(%, %) == (c /\ a = 0, c /\ a ~= 0);

			equalities(c:%):Generator Cross(T, T) == generate {
				import from T;
				for a in zero c repeat yield(a, 0);
			}

			inequalities(c:%):Generator Cross(T, T) == generate {
				import from T;
				for a in nonzero c repeat yield(a, 0);
			}
		}
	}
}

