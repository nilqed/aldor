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
----------------------------- primes63.as ----------------------------------
#include "sumit"

macro Z == SingleInteger;

Primes63: PrimeTable == add {
	-- the last 60 63-bit primes
	primes:Array Z == [_
		9223372036854773477, 9223372036854773489, 9223372036854773507,_
		9223372036854773519, 9223372036854773557, 9223372036854773561,_
		9223372036854773639, 9223372036854773783, 9223372036854773867,_
		9223372036854773899, 9223372036854773953, 9223372036854773977,_
		9223372036854773999, 9223372036854774053, 9223372036854774173,_
		9223372036854774179, 9223372036854774199, 9223372036854774233,_
		9223372036854774247, 9223372036854774257, 9223372036854774277,_
		9223372036854774307, 9223372036854774319, 9223372036854774341,_
		9223372036854774413, 9223372036854774451, 9223372036854774499,_
		9223372036854774509, 9223372036854774511, 9223372036854774559,_
		9223372036854774571, 9223372036854774587, 9223372036854774629,_
		9223372036854774679, 9223372036854774713, 9223372036854774739,_
		9223372036854774797, 9223372036854774893, 9223372036854774917,_
		9223372036854774937, 9223372036854774959, 9223372036854775057,_
		9223372036854775073, 9223372036854775097, 9223372036854775139,_
		9223372036854775159, 9223372036854775181, 9223372036854775259,_
		9223372036854775279, 9223372036854775291, 9223372036854775337,_
		9223372036854775351, 9223372036854775399, 9223372036854775417,_
		9223372036854775421, 9223372036854775433, 9223372036854775507,_
		9223372036854775549, 9223372036854775643, 9223372036854775783];

	-- 63-bit primes of the form 2^n k + 1 for n = 1,2,...,16
	fourier:Array Z == [_
		9223372036854775783, 9223372036854775549, 9223372036854775433,_
		9223372036854775057, 9223372036854775073, 9223372036854773953,_
		9223372036854771841, 9223372036854771457, 9223372036854747649,_
		9223372036854758401, 9223372036854675457, 9223372036854460417,_
		9223372036854374401, 9223372036854497281, 9223372036853235713,_
		9223372036853661697, 9223372036844421121];

	-- primitive 2^n-th roots of unity for the above fourier primes
	 roots:Array Z == [_
		9223372036854775782, 3240558518817831482, 4171426351174236828,_
		1633667126224019131, 4157847666630089467, 2221942928855380634,_
		3538733102255940697, 1716430083025891097, 3345749197117459333,_
		8514983230644668327, 9049461781042640807, 5605891926531706623,_
		1009825714493485787, 3005483215108443779, 5726005320285737278,_
		781480991878226726,  131461279243254895];

}
