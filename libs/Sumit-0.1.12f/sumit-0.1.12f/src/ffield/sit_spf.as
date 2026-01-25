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
--------------------------- sit_spf.as --------------------------------
-- Copyright (c) Manuel Bronstein 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995-97
-----------------------------------------------------------------------------

#include "sumit"

macro Z == MachineInteger;

#if ALDOC
\thistype{SmallPrimeField}
\History{Manuel Bronstein}{6/7/94}{created}
\Usage{import from \this~p}
\Params{ {\em p} & \astype{MachineInteger} & The characteristic\\ }
\Descr{\this~p implements the finite field $\ZZ / p \ZZ$ where $p\in \ZZ$
is a word--size prime.}
\begin{exports}
\category{\astype{SmallPrimeFieldCategory}}\\
\end{exports}
#endif

-- TEMPORARY: WORKAROUND FOR BUG1167
-- SmallPrimeField(p:Z): SmallPrimeFieldCategory == SmallPrimeField0 p;
SmallPrimeField(p:Z): SmallPrimeFieldCategory == SmallPrimeField0 p add;

#if SUMITTEST
---------------------- test sit__spf.as --------------------------
#include "sumittest"

macro F == SmallPrimeField 10007;

import from MachineInteger, F;

local inverse():Boolean == {
	a:F := 0;
	while zero? a repeat a := random();
	b := inv a;
	a * b = 1;
}

local exponentiate():Boolean == {
	import from Integer;
	a:F := 0;
	while zero? a repeat a := random();
	b := lift random();
	c:F := 1;
	for i in 1..b repeat c := c * a;
	a^b = c;
}

local sum():Boolean == {
	import from Integer;
	a:F := 0;
	while zero? a repeat a := random();
	b0:F := random();
	b := lift b0;
	c:F := 0;
	for i in 1..b repeat c := c + a;
	b0 * a = c;
}

stdout << "Testing sit__spf..." << endnl;
sumitTest("sum", sum);
sumitTest("inverse", inverse);
sumitTest("exponentiate", exponentiate);
stdout << endnl;
#endif

