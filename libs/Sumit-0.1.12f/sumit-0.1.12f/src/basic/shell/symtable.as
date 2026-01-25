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
---------------------- symtable.as -----------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1995
--
#include "axllib"

#if ASDOC
\thistype{SymbolTable}
\History{Manuel Bronstein}{10/01/96}{created}
\Usage{import from \this~T}
\Params{ T & BasicType & Type of the symbols in the table\\ }
\Descr{\this~T provides symbol tables where all the symbols have type T.}
\begin{exports}
apply: & (\%, String) $\to$ Partial T & Search for a symbol\\
set!: & (\%, String, T) $\to$ T & Add a symbol\\
table: & () $\to$ \% & Create an empty table\\
\end{exports}
#endif

SymbolTable(T:BasicType):with {
	apply: (%, String) -> Partial T;
#if ASDOC
\aspage{apply}
\Usage{ \name(t, x)\\t~x }
\Signature{(\%, String)}{Partial T}
\Params{
{\em t} & \% & A symbol table\\
{\em x} & String & A variable name\\
}
\Retval{Returns the value that x has in t if it is found, \failed~otherwise.}
#endif
	set!: (%, String, T) -> T;
#if ASDOC
\aspage{set!}
\Usage{ \name(t, x, v)\\t.x := v }
\Signature{(\%, String, T)}{T}
\Params{
{\em t} & \% & A symbol table\\
{\em x} & String & A variable name\\
{\em v} & T & A value\\
}
\Descr{Assigns the value v to x in t. If x already had a value in t, the
older value is lost.}
\Retval{Returns v.}
#endif
	table: () -> %;
#if ASDOC
\aspage{table}
\Usage{\name()}
\Signature{()}{\%}
\Retval{Returns an empty symbol table.}
\seealso{set!(\this)}
#endif
} == add {
	macro Rep == HashTable(String, T);
		
	import from Rep;

	table():%				== per table(=, myhash);
	set!(t:%, key:String, value:T):T	== set!(rep t, key, value);
	modulus:SingleInteger	== { import from SingleInteger; shift(1, 8); }

	myhash(s:String):SingleInteger == {
		import from Character;
		n:SingleInteger := 0;
		for i in 1..#s repeat n := (n + i * ord(s.i)) mod modulus;
		n;
	}

	apply(t:%, key:String):Partial T == {
		(found?, value) := search(rep t, key, sample);
		found? => [value];
		failed;
	}
}
