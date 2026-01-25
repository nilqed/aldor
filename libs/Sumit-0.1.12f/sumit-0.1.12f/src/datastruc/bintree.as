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
----------------------------- bintree.as ----------------------------------
#include "sumit"

#if ASDOC
\thistype{BinaryTreeCategory}
\History{Manuel Bronstein}{24/5/94}{created}
\Usage{\this~S: Category}
\Params{ {\em S} & Order & The type of the nodes }
\Descr{\this~is the category of binary search trees, not necessarily balanced.
A binary search tree is a binary tree where for any subtree, all the
elements left of its root are smaller than its root, and all the elements
right of its root are greater than its root.}
\begin{exports}
\category{Conditional}\\
\category{Aggregate S}\\
apply!: & (S $\to$ S, \%) $\to$ \% & Apply a function to all the nodes\\
apply: & (S $\to$ S, \%) $\to$ \% & Apply a function to all the nodes\\
copy: & \% $\to$ \% & Make a shallow copy of a tree\\
delete!: & (S, \%) $\to$ \% & Delete a node from a tree\\
empty: & () $\to$ \% & Create an empty tree\\
height: & \% $\to$ SingleInteger & Height of a tree\\
inOrder: & \% $\to$ List S & Inorder traversal\\
insert!: & (S, \%) $\to$ \% & Insert a node\\
insert!: & (S, S $\to$ S, \%) $\to$ \% & Insert a node \\
leaf?: & \% $\to$ Boolean & test whether a tree is a leaf\\
left: & \% $\to$ \% & Get the left subtree\\
leftMost: & \% $\to$ S & Find the leftmost leaf\\
member?: & (S, \%) $\to$ Boolean & Test whether an element is in a tree\\
postOrder: & \% $\to$ List S & Postorder traversal\\
preOrder: & \% $\to$ List S & Preorder traversal\\
reverseInOrder: & \% $\to$ List S & ReverseInorder traversal\\
right: & \% $\to$ \% & Get the right subtree\\
rightMost: & \% $\to$ S & Find the rightmost leaf\\
root: & \% $\to$ S & Find the root\\
search: & (S, \%) $\to$ Partial S & Search for an element\\
split: & (\%, S) $\to$ (List \%, List \%) & Split a tree along an element\\
tree: & S $\to$ \% & Make a tree with one node\\
\end{exports}
#endif

BinaryTreeCategory(S:Order):Category == Join(Aggregate S, Conditional) with {
	apply: (S -> S, %) -> %;
#if ASDOC
\begin{aspage}{apply}
\Usage{ \name(f, t)\\ f~t }
\Signature{(S $\to$ S, \%)}{\%}
\Params{
{\em f} & S $\to$ S & The function to apply to all the nodes\\
{\em t} & \% & A binary tree\\
}
\Descr{Makes a copy of t by applying f to all the nodes of t.}
\Retval{Returns the newly created tree. t remains unchanged.}
\begin{asex}
\begin{ttyout}
s := apply((n:Integer):Integer +-> n + n, t)
\end{ttyout}
returns a copy of t with all nodes doubled:
\asfigure{treeApply}{}
\end{asex}
\seealso{apply!(\this), copy(\this)}
\end{aspage}
#endif
	apply!: (S -> S, %) -> %;
#if ASDOC
\begin{aspage}{apply!}
\Usage{\name(f, t)}
\Signature{(S $\to$ S, \%)}{\%}
\Params{
{\em f} & S $\to$ S & The function to apply to all the nodes\\
{\em t} & \% & A binary tree\\
}
\Descr{Applies f to all the nodes of t, without modifying t itself.
This affects t only if the elements of S are mutable, and f modifies them
in place.}
\Retval{Returns t.}
\seealso{apply(\this), copy(\this)}
\end{aspage}
#endif
	copy: % -> %;
#if ASDOC
\begin{aspage}{copy}
\Usage{\name~t}
\Signature{\%}{\%}
\Params{ {\em t} & \% & A binary tree\\ }
\Retval{Returns a copy of t.}
\end{aspage}
#endif
	delete!: (S, %) -> %;
#if ASDOC
\begin{aspage}{delete!}
\Usage{\name(s, t)}
\Signature{(S,\%)}{\%}
\Params{
{\em s} & S & The node to delete\\
{\em t} & \% & A binary tree\\
}
\Descr{Deletes s from the tree t if s is a node of t.}
\Retval{Returns the updated t.}
\begin{asex}
\begin{ttyout}
t := delete!(7, t)
\end{ttyout}
removes the node 7 from t:
\asfigure{treeDelete}{}
\end{asex}
\seealso{member?(\this), search(\this)}
\end{aspage}
#endif
	empty: () -> %;
#if ASDOC
\begin{aspage}{empty}
\Usage{\name()}
\Signature{()}{\%}
\Retval{Returns an empty tree.}
\seealso{empty?(\this)}
\end{aspage}
#endif
	height: % -> SingleInteger;
#if ASDOC
\begin{aspage}{height}
\Usage{\name~t}
\Signature{\%}{SingleInteger}
\Params{ {\em t} & \% & A binary tree\\ }
\Retval{Returns the height of t, \ie one plus the length of the
longest path from the root to any leaf.}
\begin{asex}
If t is the following tree:
\asfigure{tree}{}
then
\begin{ttyout}
height t
\end{ttyout}
returns 3.
\end{asex}
\seealso{\#(Aggregate)}
\end{aspage}
#endif
	inOrder: % -> List S;
#if ASDOC
\begin{aspage}{inOrder}
\Usage{\name~t}
\Signature{\%}{List S}
\Params{ {\em t} & \% & A binary tree\\ }
\Descr{Performs an inorder traversal of t, \ie left subtree first,
then root, then right subtree.}
\Retval{Returns the list of all the nodes traversed.}
\begin{asex}
If t is the following tree:
\asfigure{tree}{}
then
\begin{ttyout}
inOrder t
\end{ttyout}
returns [6, 8, 10, 12, 14, 20].
\end{asex}
\seealso{postOrder(\this), preOrder(\this),\\ reverseInOrder(\this)}
\end{aspage}
#endif
	insert!: (S, %) -> %;
	insert!: (S, S -> S, %) -> %;
#if ASDOC
\begin{aspage}{insert!}
\Usage{ \name(s, t)\\ \name(s, f, t) }
\Signatures{
\name: & (S, \%) $\to$ \%\\
\name: & (S, S $\to$ S, \%) $\to$ \%
}
\Params{
{\em s} & S & The element to insert\\
{\em f} & S $\to$ S & The function to apply to the element if already found\\
{\em t} & \% & A binary tree\\
}
\Descr{
\name(s, t) inserts s into t if s is not already a node of t,
does not modify t otherwise.\\
\name(s, f, t) inserts s into t if s is not already a node of t,
applies f to s otherwise
(this can affect t if the elements of S are mutable and f modifies them).
}
\Retval{Returns the updated t.}
\begin{asex}
\begin{ttyout}
t := insert!(4, t)
\end{ttyout}
adds the node 4 in t:
\asfigure{treeInsert}{}
\end{asex}
\seealso{member?(\this), search(\this)}
\end{aspage}
#endif
	leaf?: % -> Boolean;
#if ASDOC
\begin{aspage}{leaf?}
\Usage{\name~t}
\Signature{\%}{Boolean}
\Params{ {\em t} & \% & A binary tree\\ }
\Retval{Returns \true~if t consists of a single leaf, \false~otherwise.}
\begin{asex}
If t is the following tree:
\asfigure{tree}{}
then
\begin{ttyout}
leaf? t
\end{ttyout}
returns \false.
\end{asex}
\end{aspage}
#endif
	left: % -> %;
#if ASDOC
\begin{aspage}{left}
\Usage{\name~t}
\Signature{\%}{\%}
\Params{ {\em t} & \% & A binary tree\\ }
\Retval{Returns the left subtree of t.}
\Errors{Error if t is empty.}
\begin{asex}
\begin{ttyout}
s := left t
\end{ttyout}
assigns the following tree to s:
\asfigure{treeLeft}{}
\end{asex}
\seealso{leftMost(\this), right(\this), rightMost(\this)}
\end{aspage}
#endif
	leftMost: % -> S;
#if ASDOC
\begin{aspage}{leftMost}
\Usage{\name~t}
\Signature{\%}{S}
\Params{ {\em t} & \% & A binary tree\\ }
\Retval{Returns the leftmost leaf of t.}
\Errors{Error if t is empty.}
\begin{asex}
If t is the following tree:
\asfigure{tree}{}
then
\begin{ttyout}
leftMost t
\end{ttyout}
returns 6.
\end{asex}
\seealso{left(\this), right(\this), rightMost(\this)}
\end{aspage}
#endif
	member?: (S, %) -> Boolean;
#if ASDOC
\begin{aspage}{member?}
\Usage{\name(s, t)}
\Signature{(S, \%)}{Boolean}
\Params{
{\em s} & S & The element to search for\\
{\em t} & \% & A binary tree\\
}
\Retval{Returns \true~if s is a node in t, \false~otherwise.}
\begin{asex}
If t is the following tree:
\asfigure{tree}{}
then
\begin{ttyout}
member?(10, t)
\end{ttyout}
returns \true, while
\begin{ttyout}
member?(11, t)
\end{ttyout}
returns \false.
\end{asex}
\seealso{insert!(\this), search(\this)}
\end{aspage}
#endif
	postOrder: % -> List S;
#if ASDOC
\begin{aspage}{postOrder}
\Usage{\name~t}
\Signature{\%}{List S}
\Params{ {\em t} & \% & A binary tree\\ }
\Descr{Performs a postorder traversal of t, \ie left subtree first, then
right subtree, then root.}
\Retval{Returns the list of all the nodes traversed.}
\begin{asex}
If t is the following tree:
\asfigure{tree}{}
then
\begin{ttyout}
postOrder t
\end{ttyout}
returns [6, 10, 8, 20, 14, 12].
\end{asex}
\seealso{inOrder(\this), preOrder(\this),\\ reverseInOrder(\this)}
\end{aspage}
#endif
	preOrder: % -> List S;
#if ASDOC
\begin{aspage}{preOrder}
\Usage{\name~t}
\Signature{\%}{List S}
\Params{ {\em t} & \% & A binary tree\\ }
\Descr{Performs a preorder traversal of t, \ie root first,
then left subtree, then right subtree.}
\Retval{Returns the list of all the nodes traversed.}
\begin{asex}
If t is the following tree:
\asfigure{tree}{}
then
\begin{ttyout}
preOrder t
\end{ttyout}
returns [12, 8, 6, 10, 14, 20].
\end{asex}
\seealso{inOrder(\this), postOrder(\this),\\ reverseInOrder(\this)}
\end{aspage}
#endif
	reverseInOrder: % -> List S;
#if ASDOC
\begin{aspage}{reverseInOrder}
\Usage{\name~t}
\Signature{\%}{List S}
\Params{ {\em t} & \% & A binary tree\\ }
\Descr{Performs a reverse inorder traversal of t, \ie right subtree first,
then root, then left subtree.}
\Retval{Returns the list of all the nodes traversed.}
\begin{asex}
If t is the following tree:
\asfigure{tree}{}
then
\begin{ttyout}
reverseInOrder t
\end{ttyout}
returns [20, 14, 12, 10, 8, 6].
\end{asex}
\seealso{inOrder(\this), postOrder(\this),\\ preOrder(\this)}
\end{aspage}
#endif
	right: % -> %;
#if ASDOC
\begin{aspage}{right}
\Usage{\name~t}
\Signature{\%}{\%}
\Params{ {\em t} & \% & A binary tree\\ }
\Retval{Returns the right subtree of t.}
\Errors{Error if t is empty.}
\begin{asex}
\begin{ttyout}
s := right t
\end{ttyout}
assigns the following tree to s:
\asfigure{treeRight}{}
\end{asex}
\seealso{left(\this), leftMost(\this), rightMost(\this)}
\end{aspage}
#endif
	rightMost: % -> S;
#if ASDOC
\begin{aspage}{rightMost}
\Usage{\name~t}
\Signature{\%}{S}
\Params{ {\em t} & \% & A binary tree\\ }
\Retval{Returns the rightmost leaf of t.}
\Errors{Error if t is empty.}
\begin{asex}
If t is the following tree:
\asfigure{tree}{}
then
\begin{ttyout}
rightMost t
\end{ttyout}
returns 20.
\end{asex}
\seealso{left(\this), leftMost(\this), rightMost(\this)}
\end{aspage}
#endif
	root: % -> S;
#if ASDOC
\begin{aspage}{root}
\Usage{\name~t}
\Signature{\%}{S}
\Params{ {\em t} & \% & A binary tree\\ }
\Retval{Returns the root of t.}
\Errors{Error if t is empty.}
\begin{asex}
If t is the following tree:
\asfigure{tree}{}
then
\begin{ttyout}
root t
\end{ttyout}
returns 12.
\end{asex}
\end{aspage}
#endif
	search: (S, %) -> Partial S;
#if ASDOC
\begin{aspage}{search}
\Usage{\name(s, t)}
\Signature{(S, \%)}{Partial S}
\Params{
{\em s} & S & The element to search for\\
{\em t} & \% & A binary tree\\
}
\Retval{If s is equal to some node of t, then returns that node,
\failed~otherwise.}
\Remarks{This can be useful if the elements of S are mutable and
the equality of S is based on one field only.
When found, the returned node can be modified by the caller.}
\begin{asex}
If t is the following tree:
\asfigure{tree}{}
then
\begin{ttyout}
search(10, t)
\end{ttyout}
returns 10, while
\begin{ttyout}
search(11, t)
\end{ttyout}
returns \failed.
\end{asex}
\seealso{insert!(\this), member?(\this)}
\end{aspage}
#endif
	split: (S, %) -> (List %, List %);
#if ASDOC
\begin{aspage}{split}
\Usage{\name(s, t)}
\Signature{(S, \%)}{(List S, List S)}
\Params{
{\em s} & S & The element to split along\\
{\em t} & \% & A binary tree\\
}
\Descr{Partitions t into 2 lists of trees ($l_-, l_+$) such that $t$
is the disjoint union of $l_-$ and $l_+$, all the nodes of all the
trees in $l_-$ are strictly less than $s$, and all the nodes of all
the trees in $l_+$ are greater than or equal to $s$.}
\Retval{Returns the 2 lists ($l_-, l_+$).}
\begin{asex}
If t is the following tree:
\asfigure{tree}{}
then
\begin{ttyout}
(lminus, lplus) := split(12, t)
\end{ttyout}
creates the following lists of trees:
\asfigure{treeSplit}{}
\end{asex}
\end{aspage}
#endif
	tree: S -> %;
#if ASDOC
\begin{aspage}{tree}
\Usage{\name~s}
\Signature{S}{\%}
\Params{ {\em s} & S & Any element\\ }
\Retval{Returns a tree with a single node s.}
\begin{asex}
\begin{ttyout}
t := tree 6
\end{ttyout}
returns the following tree:
\asfigure{tree1}{}
\end{asex}
\end{aspage}
#endif
	default {
		sample:%			== tree(sample$S);
		test(tree:%):Boolean		== not empty? tree;
		apply(f:S -> S, t:%):%		== map(f, t);
		insert!(a:S, t:%):%		== insert!(a, (x:S):S +-> x, t);
		local ncons(t:%,l:List %):List %== { t => cons(t, l); l; }
		leaf?(t:%):Boolean == t and empty? left t and empty? right t;
		leftMost(t:%):S	   == { (t0 := left t) => leftMost t0; root t; }
		rightMost(t:%):S   == { (t0 := right t) => rightMost t0;root t;}
		(p:TextWriter) << (t:%):TextWriter == apply0(p << "tree", t);

		height(t:%):SingleInteger == {
			t => max(height(left t), height(right t)) + 1;
			0
		}

		split(s:S, t:%):(List %, List %) == {
			import from List %;
			t => {
				r := tree(m := root t);
				m < s => {
					(lm, lp) := split(s, right t);
					(ncons(left t, cons(r, lm)), lp);
				}
				(lm, lp) := split(s, left t);
				(lm, cons(r, ncons(right t, lp)));
			}
			(empty(), empty());
		}

		#(t:%):SingleInteger == {
			t => #(left t) + #(right t) + 1;
			0
		}

		generator(t:%):Generator S == {
			import from List S;
			generator preOrder t;
		}

		[t:Tuple S]:% == {
			import from SingleInteger;
			tr:% := empty();
			for i in 1..length t repeat
				tr := insert!(element(t, i), tr);
			tr;
		}

		[g:Generator S]:% == {
			tr:% := empty();
			for a in g repeat tr := insert!(a, tr);
			tr;
		}

		local apply0(p:TextWriter, t:%):TextWriter == {
			import from S;
			t => {
				p := apply0(p << "(" << root t << " ", left t);
				apply0(p << " ", right t) << ")";
			}
			p << "()";
		}

		(t1:%) = (t2:%):Boolean == {
			t1 => t2 and left t1 = left t2 and right t1 = right t2;
			empty? t2;
		}

		preOrder(t:%):List S == {
			t => cons(root t, concat!(preOrder left t,
							preOrder right t));
			empty();
		}

		inOrder(t:%):List S == {
			t => concat!(inOrder left t,
					cons(root t, inOrder right t));
			empty();
		}

		reverseInOrder(t:%):List S == {
			t => concat!(reverseInOrder right t,
					cons(root t, reverseInOrder left t));
			empty();
		}

		postOrder(t:%):List S == {
			t => concat!(concat!(postOrder left t,
						postOrder right t), [root t]);
			empty();
		}

		search(a:S, t:%):Partial S == {
			t => {
				a = (r := root t) => [r];
				a < r => search(a, left t);
				search(a, right t);
			}
			failed;
		}

		member?(a:S, t:%):Boolean == {
			t => {
				a = (r := root t) => true;
				a < r => member?(a, left t);
				member?(a, right t);
			}
			false;
		}
	}
}

