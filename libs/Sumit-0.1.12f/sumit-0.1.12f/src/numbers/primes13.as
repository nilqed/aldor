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
----------------------------- sit_primes13.as ----------------------------------
#include "sumit"

macro Z	== SingleInteger;

Primes13: PrimeTable == add {
	-- the last 200 13-bit primes
	primes:Array Z == [_
		6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451,_
		6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563,_
		6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659,_
		6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733,_
		6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827,_
		6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907,_
		6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983,_
		6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069,_
		7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187,_
		7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253,_
		7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369,_
		7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487,_
		7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549,_
		7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621,_
		7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703,_
		7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817,_
		7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901,_
		7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009,_
		8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093,_
		8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191];

	-- 13-bit primes of the form 2^n k + 1 for n = 1,2,...,
	fourier:Array Z == [];

	-- primitive 2^n-th roots of unity for the above fourier primes
	roots:Array Z == [];
}
