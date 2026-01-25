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
------------------------------ sal_arith.as ---------------------------------
--
-- Types with the most basic arithmetic operations
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

#if ALDOC
\thistype{AdditiveType}
\History{Manuel Bronstein}{8/11/99}{created}
\Usage{\this: Category}
\Descr{\this~is the category of types with addition/substraction operations.}
\begin{exports}
\category{\astype{PrimitiveType}}\\
\asexp{$0$} : & \% & zero\\
\asexp{$+$} : & (\%, \%) $\to$ \% & addition\\
\asexp{$-$} : & \% $\to$ \% & opposite\\
\asexp{$-$} : & (\%, \%) $\to$ \% & substraction\\
\asexp{add!}: & (\%, \%) $\to$ \% & In--place addition\\
\asexp{minus!}: & \% $\to$ \% & In--place opposite\\
\asexp{minus!}: & (\%, \%) $\to$ \% & In--place substraction\\
\asexp{zero?}: & \% $\to$ \astype{Boolean} & test for $0$\\
\end{exports}
#endif

define AdditiveType:Category == PrimitiveType with {
	0: %;
#if ALDOC
\aspage{$0$}
\Usage{\name}
\Signature{}{\%}
\Retval{Return the $0$ constant of the type.}
#endif
	+: (%, %) -> %;
	-: % -> %;
	-: (%, %) -> %;
#if ALDOC
\aspage{$+,-$}
\astarget{$+$}
\astarget{$-$}
\Usage{$x + y$\\ $x - y$\\ $-x$}
\Signatures{
$-$: & \% $\to$ \%\\
$+,-$: & (\%, \%) $\to$ \%\\
}
\Params{ {\em x,y} & \% & elements of the type\\ }
\Retval{$x + y, x - y$ return respectively
the sum and difference $x$ with $y$, while $-x$ returns
the opposite of $x$.}
\seealso{\asexp{add!}, \asexp{minus!}}
#endif
	add!: (%, %) -> %;
	minus!:% -> %;
	minus!:(%, %) -> %;
#if ALDOC
\aspage{add!,minus!}
\astarget{add!}
\astarget{minus!}
\Usage{add!(x, y)\\ minus!(x, y)\\ minus!~x}
\Signatures{
minus!: & \% $\to$ \%\\
add!, minus!: & (\%, \%) $\to$ \%\\
}
\Params{ {\em x, y} & \% & Elements of the type\\ }
\Retval{add!($x,y$) and minus!($x,y$) returns respectively $x + y$
and $x-y$, while minus!~x returns the opposite of $x$.
In all cases, the storage used by x is allowed
to be destroyed or reused, so x is lost after this call.}
\Remarks{Those functions may cause x to be destroyed, so do not use them
unless x has been locally allocated, and is guaranteed not to share space
with other elements. Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
\seealso{\asexp{$+$},\asexp{$-$}}
#endif
	zero?: % -> Boolean;
#if ALDOC
\aspage{zero?}
\Usage{\name~x}
\Signature{\%}{\astype{Boolean}}
\Params{{\em x} & \% & an element of the type\\ }
\Retval{Returns the result of $x = 0$ using the semantics of $=$ of the type.}
#endif
	default {
		local copy?:Boolean	== % has CopyableType;
		(a:%) - (b:%):%		== a + (-b);
		zero?(a:%):Boolean	== a = 0;
		minus!(a:%):%		== -a;
		minus!(a:%, b:%):%	== a - b;

		add!(a:%, b:%):% == {
			zero? a => { copy?=>copy(b)$(% pretend CopyableType);b }
			a + b;
		}
	}
}

#if ALDOC
\thistype{ArithmeticType}
\History{Manuel Bronstein}{28/9/98}{created}
\Usage{\this: Category}
\Descr{\this~is the category of types with standard arithmetic operations.}
\begin{exports}
\category{\astype{AdditiveType}}\\
\asexp{$1$} : & \% & one\\
\asexp{$*$} : & (\%, \%) $\to$ \% & product\\
\asexp{$\hat{}$} : & (\%, \astype{MachineInteger}) $\to$ \% & exponentiation\\
\asexp{one?}: & \% $\to$ \astype{Boolean} & test for $1$\\
\asexp{times!}: & (\%, \%) $\to$ \% & In--place product\\
\end{exports}
#endif

define ArithmeticType:Category == AdditiveType with {
	1: %;
#if ALDOC
\aspage{$1$}
\Usage{\name}
\Signature{}{\%}
\Retval{Return the $1$ constant of the type.}
#endif
	*: (%, %) -> %;
	^: (%, MachineInteger) -> %;
#if ALDOC
\aspage{$\ast$,\^{}}
\astarget{$*$}
\astarget{$\hat{}$}
\Usage{$x \ast y$\\ $x$ \^{} $n$}
\Signatures{
$\ast$: & (\%, \%) $\to$ \%\\
\^{}: & (\%, \astype{MachineInteger}) $\to$ \%\\
}
\Params{
{\em x,y} & \% & elements of the type\\
{\em n} & \astype{MachineInteger} & an exponent\\
}
\Retval{$x \ast y$ returns the product of $x$ with $y$, while
$x$ \^{} $n$ returns $x$ to the power $n$.}
\seealso{\asexp{times!}}
#endif
	times!:(%, %) -> %;
#if ALDOC
\aspage{times!}
\Usage{\name(x, y)}
\Signature{(\%, \%)}{\%}
\Params{ {\em x, y} & \% & Elements of the type\\ }
\Retval{Return $xy$, where the storage used by x is allowed
to be destroyed or reused, so x is lost after this call.}
\Remarks{This function may cause x to be destroyed, so do not use it unless
x has been locally allocated, and is guaranteed not to share space
with other elements. Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
\seealso{\asexp{$*$}}
#endif
	one?: % -> Boolean;
#if ALDOC
\aspage{one?}
\Usage{\name~x}
\Signature{\%}{\astype{Boolean}}
\Params{{\em x} & \% & an element of the type\\ }
\Retval{Returns the result of $x = 1$ using the semantics of $=$ of the type.}
#endif
	default {
		local copy?:Boolean	== % has CopyableType;
		one?(a:%):Boolean	== a = 1;

		times!(a:%, b:%):% == {
			one? a => { copy?=>copy(b)$(% pretend CopyableType);b }
			a * b;
		}
	}
}

