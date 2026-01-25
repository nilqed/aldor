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
----------------------------- bstree.as ----------------------------------
#include "sumit"

#if ASDOC
\thistype{BSTree}
\History{Manuel Bronstein}{17/6/94}{created}
\Usage{import from \this~S}
\Params{ {\em S} & Order & The type of the nodes\\ }
\Descr{\this~is an implementation of binary search trees, \ie binary trees
where for each subtree t, all the nodes in the left subtree of t are
smaller than the root of t, and all the nodes in the right subtree of t
are bigger than the root of t.}
\begin{exports}
\category{BinaryTreeCategory S}\\
\end{exports}
#endif

BSTree(S:Order): BinaryTreeCategory S == add {
	macro Z   == SingleInteger;
	macro REC == Record(key:S, lft: %, rgt: %);
	macro Rep == NilRecord(key:S, lft: %, rgt: %);

	import from Rep, REC;

	local rec(x:%):REC		== record rep x;
	empty():%    			== per nil;
	empty?(t:%):Boolean		== nil? rep t;
	tree(a:S):%			== per [a, empty(), empty()];
	setRight!(t:%, t0:%):%		== rec(t).rgt := t0;
	setLeft!(t:%, t0:%):%		== rec(t).lft := t0;
	setRoot!(t:%, s:S):S		== rec(t).key := s;
	root(t:%):S			== rec(t).key;
	left(t:%):%			== rec(t).lft;
	right(t:%):%			== rec(t).rgt;
	max(t:%):S			== { (r := right t) => max r; root t; }

	apply!(f:S->S, t:%):% == {
		empty? t => t;
		r := rec t; f(r.key);
		r.lft := apply!(f, rec(t).lft);
		r.rgt := apply!(f, rec(t).rgt);
		t;
	}

	copy(t:%):% == {
		empty? t => t;
		per [root t, copy left t, copy right t];
	}

	map(f:S -> S, t:%):% == {
		empty? t => t;
		per [f root t, map(f, left t), map(f, right t)];
	}

	insert!(a:S, f: S -> S, t:%):% == {
		empty? t => tree a;
		if a = (r := root t) then f(rec(t).key)
		else if a < r then setLeft!(t, insert!(a, f, left t));
				else setRight!(t, insert!(a, f, right t));
		t;
	}

	delete!(a:S, t:%):% == {
		empty? t => t;
		a = (r := root t) => deleteRoot! t;
		if a < r then setLeft!(t, delete!(a, left t));
			else setRight!(t, delete!(a, right t));
		t;
	}

	local deleteRoot!(t:%):% == {
		empty?(t0 := left t) => right t;
		empty? right t => t0;
		setRoot!(t, m := max t0);
		setLeft!(t, delete!(m, t0));
		t;
	}
}
