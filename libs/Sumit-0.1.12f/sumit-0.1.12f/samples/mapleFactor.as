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
------------------------------ mapleFactor.as ------------------------------
--
-- This file demonstrates how to use the Maple() type of Sum^it
-- to interface selected Maple functions to aldor programs,
-- as well as how to walk down an ExpressionTree to reconstruct a value
--
-- Here, we define a type MapleIntegerFactorization, that
-- exports to Aldor clients Maple's integer factorization.
-- The function first calls 'numtheory[ifactors]' from Maple,
-- then walks down the resulting expression tree and reconstructs
-- the factorization as an element of Product(Integer).
--
-- When compiled with '-fx -dMAKETEST', this crates a test executable
-- Otherwise, this creates a type usable in other Aldor programs.
--

#include "sumit"

macro {
	Z    == Integer;
	TREE == ExpressionTree;
}

MapleIntegerFactorization: with {
	-- We use 'Partial' because any call to Maple could fail,
	-- for example if Maple is not present on the system
	-- Otherwise, this returns (u, \prod_i p_i^{e_i}) where u is sign(n)
	-- and the product is the prime factorization of |n|
	factor: Z -> Partial Cross(Z, Product Z);
} == add {
	factor(n:Z):Partial Cross(Z, Product Z) == {
		import from Boolean, String, Maple, Partial Z;
		import from TREE, List TREE, Partial TREE;

		-- create a Maple session;
		session := maple();

		-- we cannot use 'ifactor' because its results prints
		-- using backquotes (e.g. ``(2)^3) which cannot be parsed
		-- so we call 'numtheory[ifactors]' instead
		-- note that we terminate the command with ':' and not ';'
		input(session) << "numtheory[ifactors](" << n << "):";

		-- now run Maple and try to parse the result
		result := run session;
		failed? result => failed;	-- syntax error or no Maple
		-- this will be the ExpressionTree of the result
		tree := retract result;

		-- From now on we reconstruct a Product(Z) from tree:
		-- tree must be of the form [u, [[n1,e1],[n2,e2],...,[nk,ek]]]
		-- so it must have 2 arguments or we fail
		empty?(args := arguments tree) => failed;
		sign := first args;		-- must be an integer leaf
		-- since Integer has the category Parsable,
		-- it exports a function 'eval: TREE -> Partial %'
		-- we use 'eval$Z' because this function can also exist
		-- in other types and we want the one from Z only
		failed?(u := eval(sign)$Z) => failed;
		empty? rest args => failed;
		factors := first rest args;	-- must be a list of pairs
		prod:Product Z := 1;
		for pair in arguments factors repeat {
			-- pair must be of the form [m, e], representing m^e
			empty?(args := arguments pair) or empty?(rest args)
				or failed?(m := eval(first args)$Z)
				or failed?(e := eval(first rest args)$Z) =>
					return failed;
			-- accumulate m^e into the formal product
			prod := times!(prod, retract m, retract e);
		}
		[(retract u, prod)];
	}
}

-- To make a test executable
#if MAKETEST
#include "sallio"		-- imports I/O stuff
local testFactor():() == {
	import from Z, MapleIntegerFactorization;
	import from Product Z, Partial Cross(Z, Product Z);

	stdout << "Enter an integer to factor: " << flush;
	n:Z := << stdin;
	stdout << "ifactor(" << n << ") = ";
	failed?(result := factor n) => stdout << "failed!" << newline << endnl;
	(sgn, prod) := retract result;
	if sgn < 0 then stdout << "-";
	stdout << prod << newline << endnl;
}

testFactor();
#endif
