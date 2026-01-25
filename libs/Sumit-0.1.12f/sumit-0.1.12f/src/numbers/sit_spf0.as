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
--------------------------- sit_spf0.as --------------------------------
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"

macro Z == MachineInteger;

#if ALDOC
\thistype{SmallPrimeField0}
\History{Manuel Bronstein}{6/7/94}{created}
\Usage{import from \this~p}
\Params{ {\em p} & \astype{MachineInteger} & The characteristic\\ }
\Descr{\this~p is an internal implementation of the finite field
$\ZZ / p \ZZ$ where $p\in \ZZ$ is a word--size prime.
Use \astype{SmallPrimeField} instead.}
\begin{exports}
\category{\astype{SmallPrimeFieldCategory0}}\\
\end{exports}
#endif

SmallPrimeField0(p:Z): SmallPrimeFieldCategory0 == {
        -- sanity checks on the parameters
        assert(p > 1);

	add {
	Rep == Z;

	import from Rep;

	local maxhalf:Z				== maxPrime$HalfWordSizePrimes;
	0:%					== per 0;
	1:%					== per 1;
	local pp:Integer			== p::Integer;
	local p1:Integer			== prev pp;
	characteristic:Integer			== pp;
	karatsubaCutoff:Z			== 20;
	-- fftCutoff:Z				== 400;
	(a:%) = (b:%):Boolean			== rep a = rep b;
	lift(a:%):Integer			== rep(a)::Integer;
	coerce(a:Integer):%			== per machine(a mod pp);
	(a:%) / (b:%):%				== per mod_/(rep a, rep b, p);
	inv(a:%):%				== per modInverse(rep a, p);
	-(a:%):%			== { zero? a => a; per(p - rep a); }

	if p > maxhalf then {
		(a:%) * (b:%):%			== per mod_*(rep a, rep b, p);
		(a:%) + (b:%):%			== per mod_+(rep a, rep b, p);
	} else { -- we know that +/* on rep cannot overflow
		(a:%) * (b:%):%			== per((rep(a) * rep(b)) rem p);
		(a:%) + (b:%):%	== {
			p <= (c := rep a + rep b) => per(c - p);
			per c;
		}
	}

	(a:%)^(n:Integer):% == {
		zero? a => 0;
		one? a => a;
		m:Z := machine(n mod p1);
		per mod_^(rep a, m, p);
	}

	-- TEMPORARY: BUG 1181
	#:Integer		== characteristic$%;

	-- THOSE ARE BETTER THAN THE CORRESPONDING CATEGORY DEFAULTS
	zero?(a:%):Boolean	== zero? rep a;
	one?(a:%):Boolean	== one? rep a;
	add!(a:%, b:%):%	== a + b;
	times!(a:%, b:%):%	== a * b;
	coerce(a:Z):%		== per(a mod p);
	machine(a:%):Z		== rep a;
	(a:%) - (b:%):%	== { (c := rep a - rep b) < 0 => per(c + p); per c }

	-- TEMPORARY (BUG1182) DEFAULTS DON'T INLINE WELL
	minus!(a:%):%		== -a;
	}
}
