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
extend AldorInteger: with { lsbgcd: (%, %) -> %; } == add {
	lsbgcd(u:%, v:%):%		== lsbgcd0(abs u, abs v);

	-- From J.Shallit & J.Sorenson,
        --   "Analysis of a Left-Shift Binary GCD Algorithm",
	-- Journal of Symbolic Computation 17, 473-486, 1994.
	local lsbgcd0(u:%, v:%):% == {
		import from MachineInteger;
		if u < v then (u, v) := (v, u);
		lu := length u; lv := length v;
		while v > 0 repeat {
			assert(u >= v); assert(v >= 0);
			v2e1 := v2e := shift(v, lu - lv);
			if u < v2e	then v2e  := shift(v2e, -1);
					else v2e1 := shift(v2e, 1);
			t := min(u - v2e, v2e1 - u);
			if v < t then { u := t; lu := length t }
			else { u := v; v := t; lu := lv; lv := length t }
		}
		u;
	}
}

