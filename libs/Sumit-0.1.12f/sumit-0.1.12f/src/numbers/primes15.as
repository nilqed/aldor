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
----------------------------- primes15.as ----------------------------------
#include "sumit"

macro Z	== SingleInteger;

Primes15: PrimeTable == add {
	-- the last 200 15-bit primes
	primes:Array Z == [_
		30707, 30713, 30727, 30757, 30763, 30773, 30781, 30803, 30809,_
		30817, 30829, 30839, 30841, 30851, 30853, 30859, 30869, 30871,_
		30881, 30893, 30911, 30931, 30937, 30941, 30949, 30971, 30977,_
		30983, 31013, 31019, 31033, 31039, 31051, 31063, 31069, 31079,_
		31081, 31091, 31121, 31123, 31139, 31147, 31151, 31153, 31159,_
		31177, 31181, 31183, 31189, 31193, 31219, 31223, 31231, 31237,_
		31247, 31249, 31253, 31259, 31267, 31271, 31277, 31307, 31319,_
		31321, 31327, 31333, 31337, 31357, 31379, 31387, 31391, 31393,_
		31397, 31469, 31477, 31481, 31489, 31511, 31513, 31517, 31531,_
		31541, 31543, 31547, 31567, 31573, 31583, 31601, 31607, 31627,_
		31643, 31649, 31657, 31663, 31667, 31687, 31699, 31721, 31723,_
		31727, 31729, 31741, 31751, 31769, 31771, 31793, 31799, 31817,_
		31847, 31849, 31859, 31873, 31883, 31891, 31907, 31957, 31963,_
		31973, 31981, 31991, 32003, 32009, 32027, 32029, 32051, 32057,_
		32059, 32063, 32069, 32077, 32083, 32089, 32099, 32117, 32119,_
		32141, 32143, 32159, 32173, 32183, 32189, 32191, 32203, 32213,_
		32233, 32237, 32251, 32257, 32261, 32297, 32299, 32303, 32309,_
		32321, 32323, 32327, 32341, 32353, 32359, 32363, 32369, 32371,_
		32377, 32381, 32401, 32411, 32413, 32423, 32429, 32441, 32443,_
		32467, 32479, 32491, 32497, 32503, 32507, 32531, 32533, 32537,_
		32561, 32563, 32569, 32573, 32579, 32587, 32603, 32609, 32611,_
		32621, 32633, 32647, 32653, 32687, 32693, 32707, 32713, 32717,_
		32719, 32749];

	-- 15-bit primes of the form 2^n k + 1 for n = 1,2,...,12
	fourier:Array Z == [_
		30707, 30757, 30713, 31121, 30817, 32321, 31873, 31489, 32257,_
		25601, 18433, 12289];

	-- primitive 2^n-th roots of unity for the above fourier primes
	roots:Array Z == [_
		30706, 11220, 13503,  2272, 14748, 22574, 26607, 22354, 30331,_
		12725, 17660, 1331];
}
