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
--------------------------- sal_fltcat.as ----------------------------------
--
-- Category for floating point systems
--
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

macro Z == MachineInteger;

#if ALDOC
\thistype{FloatType}
\History{Manuel Bronstein}{26/7/99}{created}
\Usage{\this: Category}
\Descr{\this~is the category of types representing floats.}
\begin{exports}
\category{\astype{InputType}}\\
\category{\astype{OrderedArithmeticType}}\\
\category{\astype{OutputType}}\\
\category{\astype{SerializableType}}\\
\asexp{$/$}: & (\%, \%) $\to$ \% & division\\
\asexp{coerce}: & \astype{MachineInteger} $\to$ \% & conversion to a float\\
\asexp{fraction}: & \% $\to$ \% & fractional part\\
\asexp{truncate}: & \% $\to$ \astype{AldorInteger} & truncation\\
\end{exports}
#endif

define FloatType:Category ==
	Join(OrderedArithmeticType,InputType,OutputType,SerializableType) with {
	/: (%, %) -> %;
#if ALDOC
\aspage{$/$}
\Usage{$x / y$}
\Signature{(\%,\%)}{\%}
\Params{ {\em x,y} & \% & floats\\ }
\Retval{Returns the quotient of $x$ by $y$.}
#endif
	coerce: Z -> %;
#if ALDOC
\aspage{coerce}
\Usage{n::\%}
\Signature{\astype{MachineInteger}}{\%}
\Params{ {\em n} & \astype{MachineInteger} & a machine integer\\ }
\Retval{Returns n converted to a float.}
#endif
	float: Literal -> %;
	fraction: % -> %;
	truncate: % -> AldorInteger;
#if ALDOC
\aspage{fraction,truncate}
\astarget{fraction}
\astarget{truncate}
\Usage{fraction~x\\ truncate~x}
\Signatures{
fraction: & \% $\to$ \%\\
truncate: & \% $\to$ \astype{AldorInteger}\\
}
\Params{ {\em x} & \% & a float\\ }
\Retval{truncate($x$) returns $n$ such that $n x \ge 0$ and
$|n| \le |x| < |n| + 1$, while fraction($x$) returns $x - \mbox{truncate}(x)$.}
#endif
	default {
	local value(c:Character):Z	== ord(c)::Z - 48;
        local plus:Character		== { import from Z; char  43; }
        local minus:Character		== { import from Z; char  45; }
        local dot:Character		== { import from Z; char  46; }
	local E:Character		== { import from Z; char  69; }
	local e:Character		== { import from Z; char 101; }
	local ten:%			== { import from Z; 10::% }

	<< (p:TextReader):% == {
		import from Character, Boolean;
		local c:Character;
		while space?(c := << p) repeat {};
		c = plus => read p;
		c = minus => - read p;
		c = dot => scanfrac(p, 0, false);
		digit? c => scan(p, value(c)::%);
		0;
	}

	-- the sign (+/-) has been read, spaces are allowed
	local read(p:TextReader):% == {
		import from Character, Boolean;
		local c:Character;
		while space?(c := << p) repeat {};
		c = dot => scanfrac(p, 0, false);
		digit? c => scan(p, value(c)::%);
		0;
	}

	-- the sign (+/-) and first digit before . have been read,
	-- no spaces allowed
	-- n = value already read
	local scan(p:TextReader, n:%):% == {
		import from Z, Character, Boolean;
		local c:Character;
		while digit?(c := << p) repeat n := ten * n + value(c)::%;
		c = dot => scanfrac(p, n, true);
		c = e or c = E => {
			-- do not use exponentiation from % since it is not
			-- supported in the interactive loop (C function)
			import from BinaryPowering(%, Z);
			m:Z := << p;
			m < 0 => n / binaryExponentiation(ten, -m);
			n * binaryExponentiation(ten, m);
		}
		push!(c, p);
		n;
	}

	-- the . has been read, no spaces allowed
	-- n = value before the .
	local scanfrac(p:TextReader, n:%, allowE?:Boolean):% == {
		local c:Character;
		f:% := 0;
		ex:% := 1;
		tenth:% := 0.1;
		while digit?(c := << p) repeat {
				allowE? := true;
				ex := ex * tenth;
				f := f + value(c)::% * ex;
		}
		f := f + n;
		allowE? and (c = e or c = E) => {
			-- do not use exponentiation from % since it is not
			-- supported in the interactive loop (C function)
			import from BinaryPowering(%, Z);
			m:Z := << p;
			m < 0 => f / binaryExponentiation(ten, -m);
			f * binaryExponentiation(ten, m);
		}
		push!(c, p);
		f;
	}
	}
}
