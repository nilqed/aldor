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
----------------------------- avltree.as ----------------------------------
#include "sumit.as"

#if ASDOC
\thistype{AVLTree}
\History{Manuel Bronstein}{24/5/94}{created}
\Usage{import from \this~S}
\Params{ {\em S} & Order & The type of the nodes\\ }
\Descr{\this~is an implementation of AVL trees, \ie balanced binary search
trees.}
\begin{exports}
\category{BinaryTreeCategory S}\\
\end{exports}
#endif

AVLTree(S:Order): BinaryTreeCategory S == add {
	macro Z   == SingleInteger;

	-- bal = height(right) - height(left)
	macro REC == Record(key:S, lft: %, rgt: %, bal: Z);
	-- TEMPORARY: NilRec not usable with 1.0.3
	--macro Rep == NilRecord(key:S, lft: %, rgt: %, bal: Z);
	macro Rep == Record(key:S, lft: %, rgt: %, bal: Z);

	import from Rep, REC;

	-- TEMPORARY: NilRec not usable with 1.0.3
	--rec(x:%):REC			== record rep x;
	--empty():%    			== per nil;
	--empty?(t:%):Boolean		== nil? rep t;
	rec(x:%):REC			== rep x;
	empty():%    			== per(nil$Pointer pretend Rep);
	empty?(t:%):Boolean		== nil?(rep(t) pretend Pointer)$Pointer;
	tree(a:S):%			== per [a, empty(), empty(), 0];
	balance(t:%):Z			== rec(t).bal;
	setRight!(t:%, t0:%):%		== rec(t).rgt := t0;
	setLeft!(t:%, t0:%):%		== rec(t).lft := t0;
	root(t:%):S			== rec(t).key;
	left(t:%):%			== rec(t).lft;
	right(t:%):%			== rec(t).rgt;

	setBalance!(t:%, n:Z):Z	== {
		ASSERT(n < 2); ASSERT(n > -2);
		rec(t).bal := n;
	}

	apply!(f:S->S, t:%):% == {
		empty? t => t;
		r := rec t; f(r.key);
		r.lft := apply!(f, rec(t).lft);
		r.rgt := apply!(f, rec(t).rgt);
		t;
	}

	copy(t:%):% == {
		empty? t => t;
		per [root t, copy left t, copy right t, balance t];
	}

	map(f:S -> S, t:%):% == {
		empty? t => t;
		per [f root t, map(f, left t), map(f, right t), balance t];
	}

	delete!(a:S, t:%):% == {
		empty? t => t;
		(b, t) := delete0!(a, t);
		t;
	}

	-- returns true if a the height decreased, false otherwise
	-- rebalances t if needed
	-- returns a pointer to the modified tree
	-- TEMPORARY
	delete0!(a:S, t:%):(Boolean, %) == (false, t);

	insert!(a:S, f: S -> S, t:%):% == {
		empty? t => tree a;
		(b, t) := insert0!(a, f, t);
		t;
	}

	-- returns true if a the height increased, false otherwise
	-- rebalances t if needed
	-- returns a pointer to the modified tree
	insert0!(a:S, f:S -> S, t:%):(Boolean, %) == {
		a = (r := root t) => { f(rec(t).key); (false, t) };
		a < r => {
			empty?(t0 := left t) => {
				setLeft!(t, tree a); 
				setBalance!(t, balance t - 1);
				(empty? right t, t);
			}
			(increased?, t0) := insert0!(a, f, t0);
			increased? => {
				setBalance!(t, n := balance t - 1);
				n < -1 => lrebalance(t, t0);
				(n < 0, t);
			}
			setLeft!(t, t0);
			(false, t);
		}
		empty?(t0 := right t) => {
			setRight!(t, tree a);
			setBalance!(t, balance t + 1);
			(empty? left t, t);
		}
		(increased?, t0) := insert0!(a, f, t0);
		increased? => {
			setBalance!(t, n := balance t + 1);
			n > 1 => rrebalance(t, t0);
			(n > 0, t);
		}
		setRight!(t, t0);
		(false, t);
	}

	-- t0 must be left t
	lrebalance(t:%, t0:%):(Boolean, %) == {
		ASSERT(t0 = left t);
		-1 = balance t0 => {	-- LL rotation
			setLeft!(t, right t0);
			setRight!(t0, t);
			setBalance!(t, 0);
			setBalance!(t0, 0);
			(false, t0);
		}
		t1 := right t0;		-- double LR rotation
		setRight!(t0, left t1);
		setLeft!(t, right t1);
		setLeft!(t1, t0);
		setRight!(t1, t);
		n := balance t1;
		setBalance!(t, { n < 0 => 1 ; 0 });
		setBalance!(t0,{ n > 0 => -1 ; 0 });
		setBalance!(t1, 0);
		(false, t1);
	}

	-- t0 must be right t
	rrebalance(t:%, t0:%):(Boolean, %) == {
		ASSERT(t0 = right t);
		1 = balance t0 => {	-- RR rotation
			setRight!(t, left t0);
			setLeft!(t0, t);
			setBalance!(t, 0);
			setBalance!(t0, 0);
			(false, t0);
		}
		t1 := left t0;	-- double RL rotation
		setLeft!(t0, right t1);
		setRight!(t, left t1);
		setRight!(t1, t0);
		setLeft!(t1, t);
		n := balance t1;
		setBalance!(t, { n > 0 => -1 ; 0 });
		setBalance!(t0, { n < 0 => 1 ; 0 });
		setBalance!(t1, 0);
		(false, t1);
	}
}
