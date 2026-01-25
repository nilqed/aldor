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
-------------------------------- algebrauid.as -----------------------------
--
-- Definition of constants used by operators, parsers and the cutoff function
--
-- Copyright (c) Manuel Bronstein 1994-2002
-- Copyright (c) INRIA 1997-2002, Version 1.0.1
-- Logiciel Algebra (c) INRIA 1997-2002, dans sa version 1.0.1
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-1997
-----------------------------------------------------------------------------

macro {
	UID__PLUS	== 100;
	UID__TIMES	== 200;
	UID__EXPT	== 300;
	UID__FACTORIAL	== 310;
	UID__DIVIDE	== 400;
	UID__MINUS	== 500;
	UID__MATRIX	== 1000;
	UID__VECTOR	== 1010;
	UID__LIST	== 1020;
	UID__LLIST	== 1021;
	UID__COMPLEX	== 1030;
	UID__EQUAL	== 1100;
	UID__NOTEQUAL	== 1110;
	UID__AND	== 1120;
	UID__OR		== 1121;
	UID__NOT	== 1122;
	UID__IF		== 1130;
	UID__CASE	== 1140;
	UID__LESSEQUAL	== 1150;
	UID__LESSTHAN	== 1160;
	UID__MOREEQUAL	== 1170;
	UID__MORETHAN	== 1180;
	UID__BIGO	== 1190;
	UID__PREFIX	== 10000;
	UID__ASSIGN	== 10010;
	UID__SUBSCRIPT	== 10020;

	TEXPREC__PLUS	== 1000;
	TEXPREC__TIMES	== 2000;
	TEXPREC__DIVIDE	== 2500;
	TEXPREC__MINUS	== 2700;
	TEXPREC__EXPT	== 3000;

	CUTOFF__KARAMULT== 0;
	CUTOFF__FFTMULT	== 1;
	CUTOFF__QUOTBY	== 10;
	CUTOFF__DIVIDEBY== 11;
	CUTOFF__DIVIDE	== 12;

	INFIX2(f,p,l,n) == { f(p,first l); p << n; f(p,first rest l)};
}
