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
----------------------------- strtable.as ----------------------------------
#include "sumit.as"

#if ASDOC
\thistype{StringTable}
\History{Manuel Bronstein}{17/6/94}{created}
\Usage{import from \this}
\Descr{A \this~is a file-based table of strings indexed by integer keys.}
\begin{exports}
error: & SingleInteger $\to$ Exit & causes an error with an indexed message\\
string: & SingleInteger $\to$ String &
gets the string associated with a given key\\
stringTable: & FileName $\to$ Boolean & opens the specified string table\\
\end{exports}
#endif

macro Z == SingleInteger;

StringTable: with {
	error: Z -> Exit;
#if ASDOC
\begin{aspage}{error}
\Usage{\name~n}
\Signature{SingleInteger}{Exit}
\Params{ {\em n} & SingleInteger & The index of the desired error message\\ }
\Descr{Causes an error but with the string indexed by n.}
\end{aspage}
#endif
	string: Z -> String;
#if ASDOC
\begin{aspage}{string}
\Usage{\name~n}
\Signature{SingleInteger}{String}
\Params{ {\em n} & SingleInteger & The index of the desired string\\ }
\Retval{Returns the string associated with n, loading it from the external file
if needed. Returns the empty string if n does not correspond to any string.}
\end{aspage}
#endif
	stringTable: FileName -> Boolean;
#if ASDOC
\begin{aspage}{stringTable}
\Usage{\name~s}
\Signature{FileName}{Boolean}
\Params{
{\em s} & FileName & The name of the file containing the string table\\
}
\Descr{Opens the specified file which is expected to contain a string table.}
\Retval{Returns \true~if the file cannot be opened or if it is not a valid
string table, \false~otherwise.}
\begin{asex}
This code segment sets the string table to {\em language}.str
where {\em language} is the first command line argument, {\em english} by
default. It then prints a welcome message in the appropriate language.
\begin{ttyout}
macro MSG_WELCOME == 100;

init():TextWriter == {
        import from SingleInteger, Array String, CommandLine, StringTable;
        n := #arguments;
        s := { zero? n => "english"; arguments.1 };
        stringTable filename("",s,"str") => error "Cannot open string table!";
        print << string MSG_WELCOME << newline;
}
\end{ttyout}
\end{asex}
\end{aspage}
#endif
} == add {
	R: Order with {
		rec:  (Z, Z, Z, String) -> %;
		key:   % -> Z;
		length:% -> Z;
		offset:% -> Z;
		value: % -> String;
		setValue!: (%, String) -> %;
	} == add {
		macro  Rep == Record(ky:Z, len:Z, off:Z, val:String);
		import from Rep;
		sample:%			== rec(0, 0, 0, "");
		key(r:%):Z			== rep(r).ky;
		length(r:%):Z			== rep(r).len;
		offset(r:%):Z			== rep(r).off;
		value(r:%):String		== rep(r).val;
		(r:%) = (s:%):Boolean		== key r = key s;
		(r:%) > (s:%):Boolean		== key r > key s;

		rec(k:Z, n:Z, m:Z, v:String):% == {
			ASSERT(n >= 0);
			ASSERT(m >= 0);
			per [k, n, m, v];
		}

		setValue!(r:%, v:String):% == {
			rep(r).val := v;
			rep(r).off := 0;
			r;
		}

		(p:TextWriter) << (r:%):TextWriter == {
			p := p << key r << "&" << length r << "&";
			p << offset r << "&" << value r;
		}
	}

	import from R, AVLTree R, Reference AVLTree R, FileName, InFile,
			StandardUtilities;
	inline from R, AVLTree R, Reference AVLTree R, FileName, InFile,
			StandardUtilities;

	tableName:Reference(FileName) := ref filename "";
	table:Reference(AVLTree R) := ref empty();

	error(n:SingleInteger):Exit == error string n;

	stringTable(s:FileName):Boolean == {
		import from SingleInteger;
		not open?(fp := open s) => true;
		macro SIGN == "STRING TABLE";
		sign:String := getstring(fp, #SIGN);
		ok := (sign = SIGN) and ((sz := getint fp) >= 0);
		if ok then {
			t:AVLTree R := empty();
			for i in 1..sz repeat {
				k := getint fp;
				ln := getint fp;
				pos := getint fp;
				t := insert!(rec(k, ln, pos, ""), t);
			}
			table() := t;
			tableName() := filename unparse s;
		}
		close fp;
		not ok;
	}

	string(n:Z):String == {
		import from Partial R;
		failed?(r := search(rec(n, 0, 0, ""), table())) => "";
		rc := retract r;
		zero?(pos := offset rc) => value rc;
		not open?(fp := open tableName()) => "";
		seek(fp, pos) => { close fp; ""; }
		setValue!(rc, s := getstring(fp, length rc));
		close fp;
		s;
	}
}
