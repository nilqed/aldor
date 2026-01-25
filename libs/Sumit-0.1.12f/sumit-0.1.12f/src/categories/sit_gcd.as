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
------------------------------- sit_gcd.as ----------------------------------
-- Copyright (c) Manuel Bronstein 1994
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{GcdDomain}
\History{Manuel Bronstein}{13/12/94}{created}
\Usage{\this: Category}
\Descr{\this~is the category of commutative Gcd domains.}
\begin{exports}
\category{\astype{IntegralDomain}}\\
\asexp{gcd}: & (\%, \%) $\to$ \% & Gcd of $2$ elements\\
\asexp{gcd}: & \astype{List} \% $\to$ \% & Gcd of several elements\\
% \asexp{gcd}: & \builtin{Tuple} \% $\to$ \% & Gcd of several elements\\
\asexp{gcd!}: & (\%, \%) $\to$ \% & In-place gcd of $2$ elements\\
\asexp{gcdquo}: & (\%, \%) $\to$ (\%, \%, \%) & Gcd with quotients\\
\asexp{gcdquo}:
& \astype{List} \% $\to$ (\%, \astype{List} \%) & Gcd with quotients\\
\asexp{lcm}: & (\%, \%) $\to$ \% & Lcm of $2$ elements\\
\asexp{lcm}: & \astype{List} \% $\to$ \% & Lcm of several elements\\
% \asexp{lcm}: & \builtin{Tuple} \% $\to$ \% & Lcm of several elements\\
\end{exports}
#endif

define GcdDomain: Category == IntegralDomain with {
	gcd: (%, %) -> %;
	gcd: List % -> %;
	-- gcd: Tuple % -> %;
#if ALDOC
\aspage{gcd}
% \Usage{\name($x_1,x_2$)\\\name($x_1, \dots, x_n$)\\ \name~[$x_1, \dots, x_n$]}
\Usage{\name($x_1,x_2$)\\ \name~[$x_1, \dots, x_n$]}
\Signatures{
\name: & (\%, \%) $\to$ \%\\
\name: & \astype{List} \% $\to$ \%\\
% \name: & \builtin{Tuple} \% $\to$ \%\\
}
\Params{ {\em $x_i$} & \% & Elements of the ring\\ }
\Retval{Returns $\gcd(x_1,\dots,x_n)$, a generator of the ideal
$(x_1,\dots,x_n)$.}
\Remarks{With certain types, for example polynomials, the n-ary version
can be more efficient than iterating the binary version.}
\seealso{\asexp{gcd!}, \asexp{gcdquo}, \asexp{lcm}}
#endif
	gcd!: (%, %) -> %;
#if ALDOC
\aspage{gcd!}
\Usage{\name($x_1,x_2$)}
\Signature{(\%, \%)}{\%}
\Params{ {\em $x_1, x_2$} & \% & Elements of the ring\\ }
\Retval{Returns $\gcd(x_1,x_2)$, a generator of the ideal $(x_1,x_2)$.
The storage used by $x_1$ and $x_2$ is allowed
to be destroyed or reused, so $x_1$ and $x_2$ are lost after this call.}
\Remarks{This function may cause $x_1$ and $x_2$ to be destroyed,
so do not use it unless $x_1$ and $x_2$ have been locally allocated,
and are guaranteed not to share space with other elements.
Some functions are not necessarily copying their
arguments and can thus create memory aliases.}
\seealso{\asexp{gcd}, \asexp{gcdquo}, \asexp{lcm}}
#endif
	gcdquo: (%, %) -> (%, %, %);
	gcdquo: List % -> (%, List %);
#if ALDOC
\aspage{gcdquo}
\Usage{\name($x_1,x_2$)\\ \name~[$x_1,\dots,x_n$]}
\Signatures{
\name: & (\%,\%) $\to$ (\%,\%,\%)\\
\name: & \astype{List} \% $\to$ (\%, \astype{List} \%)\\
}
\Params{ {\em $x_i$} & \% & Elements of the ring\\ }
\Retval{
\name($x_1,x_2$) returns $(g, y_1, y_2)$ where $g = \gcd(x_1, x_2)$,
$x_1 = g y_1$ and $x_2 = g y_2$,\\
\name($[x_1,\dots,x_n]$) returns $(g, [y_1,\dots,y_n])$ where
$g = \gcd(x_1,\dots,x_n)$ and $x_i = g y_i$.
}
\Remarks{With certain types, for example polynomials, the n-ary version
can be more efficient than iterating the binary version.}
\seealso{\asexp{gcd}}
#endif
	lcm: (%, %) -> %;
	lcm: List % -> %;
	--lcm: Tuple % -> %;
#if ALDOC
\aspage{lcm}
% \Usage{\name($x_1,x_2$)\\\name($x_1, \dots, x_n$)\\ \name~[$x_1, \dots, x_n$]}
\Usage{\name($x_1,x_2$)\\ \name~[$x_1, \dots, x_n$]}
\Signatures{
\name: & (\%, \%) $\to$ \%\\
\name: & \astype{List} \% $\to$ \%\\
% \name: & \builtin{Tuple} \% $\to$ \%\\
}
\Params{ {\em $x_i$} & \% & Elements of the ring\\ }
\Retval{Returns $\mbox{lcm}(x_1,\dots,x_n)$, a least common multiple
of $x_1,\dots,x_n$.}
\Remarks{With certain types, for example polynomials, the n-ary version
can be more efficient than iterating the binary version.}
\seealso{\asexp{gcd}}
#endif
	default {
		--gcd(t:Tuple %):%	== gcd list t;
		--lcm(t:Tuple %):%	== lcm list t;
		gcd!(a:%, b:%):%	== gcd(a, b);

		lcm(a:%, b:%):% == {
			(g, aa, bb) := gcdquo(a, b);
			aa * b;
		}

		-- note: lcm/l * gcd/l is NOT always  */l if #l > 2
		-- however, lcm(a_1,...,a_n) = g lcm(b_1,...,b_n)
		-- where g = gcd(a_1,...,a_n) and b_i = a_i / g
		-- uses iterative lcm for the b_i's
		lcm(l:List %):%	== {
			import from Boolean;
			empty? l => 1;
			(g, quotients) := gcdquo l;
			m := first quotients;
			while ~empty?(quotients := rest quotients) repeat
				m := lcm(m, first quotients);
			g * m;
		}

		-- default is compute the gcd, then divide
		-- some gcd algorithms yield the cofactors (e.g. modgcd/heugcd)
		gcdquo(a:%, b:%):(%, %, %) == {
			unit?(g := gcd(a, b)) => (1, a, b);
			(g, quotient(a, g), quotient(b, g));
		}

		gcdquo(l:List %):(%, List %) == {
			unit?(g := gcd l) => (1, l);
			(g, [quotient(a, g) for a in l]);
		}

		-- default is iterative gcd
		-- must be coded specially where faster is possible (e.g. K[X])
		gcd(l:List %):% == {
			import from Boolean;
			unit?(g := first l) => 1;
			while ~empty?(l := rest l) repeat {
				g := gcd(g, first l);
				unit? g => return 1;
			}
			g;
		}
	}
}
