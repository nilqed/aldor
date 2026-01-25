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
----------------------------- table.as ----------------------------------
#include "sumit.as"

#if ASDOC
\thistype{Table}
\History{Manuel Bronstein}{29/5/94}{created}
\Usage{import from \this(Key, Value)}
\Params{
{\em Key} & Order & The type of the keys\\
{\em Value} & BasicType & The type of the entries\\
}
\Descr{A \this~is a collection of values indexed by arbitrary keys.}
\begin{exports}
\category{BasicType}\\
apply: & (\%, Key) $\to$ Partial Value & access an element with a given key\\
empty: & () $\to$ \% & create an empty table\\
set!: & (\%, Key, Value) $\to$ Value & enter an element with a given key\\
\end{exports}
#endif

Table(K:Order, V:BasicType): BasicType with {
	apply: (%, K) -> Partial V;
#if ASDOC
\begin{aspage}{apply}
\Usage{ \name(t, k)\\ t~k }
\Signature{(\this(K,V), K)}{Partial V}
\Params{
{\em t} & \this(K,V) & A table\\
{\em k} & K & A key\\
}
\Retval{Returns the value associated to k in t if there is one,
\failed~otherwise.}
\begin{asex}
If t of type Table(String, Integer) is the table:
\begin{center}
\begin{tabular}{l|l}
Key & Entry\\
``James'' & 120\\
``Alfred'' & 40\\
``Linda'' & 70\\
\end{tabular}
\end{center}
then
\begin{ttyout}
t("Alfred");
\end{ttyout}
returns $40$, while
\begin{ttyout}
t("Susan");
\end{ttyout}
returns \failed.
\end{asex}
\end{aspage}
#endif
	empty: () -> %;
#if ASDOC
\begin{aspage}{empty}
\Usage{\name()}
\Signature{()}{\this(K,V)}
\Retval{Returns an empty table.}
\seealso{empty?(\this)}
\end{aspage}
#endif
	set!: (%, K, V) -> V;
#if ASDOC
\begin{aspage}{set!}
\Usage{ \name(t, k, v)\\ t.k := v }
\Signature{(\this(K,V), K, V)}{V}
\Params{
{\em t} & \this(K,V) & A table\\
{\em k} & K & A key\\
{\em v} & v & The value to set\\
}
\Descr{Associates the value v to k in t. Any previous associacion of k in t
is lost.}
\Retval{Returns v.}
\begin{asex}
If t of type Table(String, Integer) is the table:
\begin{center}
\begin{tabular}{l|l}
Key & Entry\\
``James'' & 120\\
``Alfred'' & 40\\
``Linda'' & 70\\
\end{tabular}
\end{center}
then after the call
\begin{ttyout}
t("Susan") := 400;
\end{ttyout}
t is the following table:
\begin{center}
\begin{tabular}{l|l}
Key & Entry\\
``James'' & 120\\
``Alfred'' & 40\\
``Linda'' & 70\\
``Susan'' & 400\\
\end{tabular}
\end{center}
\end{asex}
\end{aspage}
#endif
} == add {
	R: Order with {
		pair: (K, V) -> %;
		key:   % -> K;
		value: % -> V;
		setValue!: (%, V) -> %;
	} == add {
		macro  Rep == Record(ky:K, val:V);
		import from Rep;
		sample:%		== pair(sample$K, sample$V);
		pair(k:K, v:V):%	== per [k, v];
		key(r:%):K		== rep(r).ky;
		value(r:%):V		== rep(r).val;
		(r:%) = (s:%):Boolean	== key r = key s;
		(r:%) > (s:%):Boolean	== key r > key s;
		setValue!(r:%, v:V):%	== { rep(r).val := v; r }

		(p:TextWriter) << (r:%):TextWriter ==
			p << key r << " & " << value r;
	}

	-- wraps a reference around the tree since an exported set! forces
	-- this type to be mutable.
	macro Rep == Reference AVLTree R;
	import from R, AVLTree R, Rep;

	tree(t:%):AVLTree R		== rep(t)();
	table(t:AVLTree R):%		== per ref t;
	dummy:V				== sample;
	sample:%			== table tree(sample$R);
	empty():%			== table empty();
	changeValue(v:V):(R -> R)	== (r:R):R +-> setValue!(r, v);

	apply(t:%, k:K):Partial V == {
		import from Partial R;
		failed?(r := search(pair(k, dummy), tree t)) => failed;
		[value retract r]
	}

	set!(t:%, k:K, v:V):V == {
		rep(t)() := insert!(pair(k, v), changeValue v, tree t);
		v;
	}

	(p:TextWriter) << (t:%):TextWriter == {
		import from List R;
		p := p << "\begin{tabular}{l|l} Key & Entry\\" << newline;
		for r in inOrder tree t repeat p := p << r << " \\";
		p << "\end{tabular}"
	}

	(t:%) = (s:%):Boolean == tree t = tree s   -- incorrect but ok for now
}
