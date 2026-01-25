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
------------------------------- nilrec.as ----------------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1994

#include "sumit"

#if ASDOC
\thistype{NilRecord}
\History{Manuel Bronstein}{5/8/94}{created}
\Usage{import from \this~T}
\Params{ {\em T} & Tuple Type & The fields of the record }
\Descr{\this~provides records which are allowed to be nil.}
\begin{exports}
bracket: & T $\to$ \% &
constructs a new record value\\
coerce: & Record T $\to$ \% &
converts a record to a NilRecord\\
eq?: & (\%, \%) $\to$ Boolean &
test whether 2 records share the same locations\\
nil: & \% & the nil pointer\\
nil?: & \% $\to$ Boolean &
test whether a record is the nil pointer\\
record: & \% $\to$ Record T &
converts a NilRecord to a record if it is not nil\\
\end{exports}
#endif

NilRecord(T:Tuple Type): with {
	bracket: T -> %;
#if ASDOC
\begin{aspage}{bracket}
\Usage{ \name($a_1,\dots,a_n$)\\ $[a_1,\dots,a_n]$ }
\Signature{T}{\this~T}
\Params{
{\em $a_1,\dots,a_n$} & ($T_1,\dots,T_n)$ &
the fields of the record to construct\\
}
\Retval{Returns a record with $a_1,\dots,a_n$ as fields.}
\end{aspage}
#endif
	coerce: Record T -> %;
#if ASDOC
\begin{aspage}{coerce}
\Usage{\name~r\\ r::\this(T) }
\Signature{Record T}{\this~T}
\Params{ {\em r} & Record T & The record to convert\\ }
\Retval{Returns r as a NilRecord.}
\end{aspage}
#endif
	eq?: (%, %) -> Boolean;
#if ASDOC
\begin{aspage}{eq?}
\Usage{\name(r, s)}
\Signature{(\this~T, \this~T)}{Boolean}
\Retval{Returns \true~if both records are at the same memory location,
\false~otherwise.}
\end{aspage}
#endif
	nil: %;
#if ASDOC
\begin{aspage}{nil}
\Usage{\name}
\Signature{}{\this~T}
\Retval{Returns the nil pointer as a record.}
\seealso{nil?(\this)}
\end{aspage}
#endif
	nil?: % -> Boolean;
#if ASDOC
\begin{aspage}{nil?}
\Usage{\name~r}
\Signature{\this~T}{Boolean}
\Params{ {\em r} & \this~T & The record to test\\ }
\Retval{Returns \true~if r is the nil pointer, \false~otherwise.}
\seealso{nil(\this)}
\end{aspage}
#endif
	record: % -> Record T;
#if ASDOC
\begin{aspage}{record}
\Usage{\name~r}
\Signature{\this~T}{Record T}
\Params{ {\em r} & \this~T & The record to convert\\ }
\Retval{Returns r as a record if it is not the nil pointer, error otherwise.}
\end{aspage}
#endif
} == add {
	macro Rep == Pointer;

	import from Rep;

	eq?(r:%, s:%):Boolean	== rep r = rep s;
	nil?(r:%):Boolean	== nil? rep r;
	nil:%			== per(nil$Pointer);
	coerce(r:Record T):%	== per(r pretend Pointer);
	record(r:%):Record T	== { ASSERT(not nil? r); r pretend Record T; }
	[t:T]:%			== { import from Record(T); [t]@Record(T)::%; }
}

#if SUMITTEST
---------------------- test nilrec.as --------------------------
#include "sumittest"

macro {
	REC == Record(a:SingleInteger, b:String);
	NREC == NilRecord(a:SingleInteger, b:String);
}

nilrec():Boolean == {
	import from SingleInteger, String, REC, NREC;
	r1:REC := [5, "hello"];
	n1:NREC := [5, "hello"];
	r2 := record n1;
	n2 := r1::NREC;
	r3 := record n2;
	r1.a=r2.a and r1.b=r2.b and r2.a=r3.a and r2.b=r3.b and ~nil? n2;
}

print << "Testing nilrec..." << newline;
sumitTest("nilrec", nilrec);
print << newline;
#endif

