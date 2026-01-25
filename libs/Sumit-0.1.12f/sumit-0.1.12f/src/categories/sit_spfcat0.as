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
-------------------------- sit_spfcat0.as ------------------------------
-- Copyright (c) Manuel Bronstein 1998
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-----------------------------------------------------------------------------

#include "sumit"

#if ALDOC
\thistype{SmallPrimeFieldCategory0}
\History{Manuel Bronstein}{15/12/98}{created}
\Usage{\this: Category}
\Descr{\this~is the category for prime fields of the form $\ZZ / p \ZZ$
where $p \in \ZZ$ is a machine prime.}
\begin{exports}
\category{\astype{PrimeFieldCategory0}}\\
\asexp{coerce}:
& \astype{MachineInteger} $\to$ \% & conversion to a field element\\
\asexp{discreteLogTable}:
& \builtin{Cross}(A, A, \astype{Boolean}) & discrete log table if available\\
\asexp{machine}:
& \% $\to$ \astype{MachineInteger} & conversion to a machine integer\\
\end{exports}
\begin{aswhere}
A &==& \astype{PrimitiveArray} \astype{MachineInteger}\\
\end{aswhere}
#endif

macro {
	I == MachineInteger;
	A == PrimitiveArray;
}

define SmallPrimeFieldCategory0: Category == PrimeFieldCategory0 with {
	coerce: I -> %;
	machine: % -> I;
#if ALDOC
\aspage{coerce,machine}
\astarget{coerce}
\astarget{machine}
\Usage{n::\%\\ machine~m}
\Signatures{
coerce: & \astype{MachineInteger} $\to$ \%\\
machine: & \% $\to$ \astype{MachineInteger}\\
}
\Params{
{\em m} & \% & an element of the field\\
{\em n} & \astype{MachineInteger} & a machine integer\\
}
\Retval{n::\% returns n as an element of the field and machine(m)
returns m as a \astype{MachineInteger}.}
#endif
	discreteLogTable: Cross(A I, A I, Boolean);
#if ALDOC
\aspage{discreteLogTable}
\Usage{((log, exp, ok?) := \name}
\Signature{}{\builtin{Cross}(A, A, \astype{Boolean})}
\begin{aswhere}
A &==& \astype{PrimitiveArray} \astype{MachineInteger}\\
\end{aswhere}
\Retval{Returns (log, exp, ok?) such that if ok? is \true,
then exp.i is $g^i$ and log.i is $\log_g(i)$ where $g$ is a
generator of the multiplicative of the group ($g$ is stored in exp.1).}
#endif
	default {
		coerce(n:I):%	== { import from Integer; n::Integer::%; }
		machine(a:%):I	== { import from Integer; machine lift a; }

		discreteLogTable:Cross(A I, A I, Boolean) == {
			import from Boolean, I, A I;
			(new 0, new 0, false);
		}
	}
}
