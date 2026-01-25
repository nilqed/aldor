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
------------------------------   vect.as   ------------------------------
#include "sumit"

macro SI   == SingleInteger;

#if ASDOC
\thistype{Vector}
\History {Marco Codutti}{10 May 1995}{created.}
\Usage   {import from \this~R}
\Params  {{\em R} & SumitRing & The coefficient ring of the vectors.}
\Descr   {\this~is an implementation of vectors.}
\begin{exports}
SumitType \\
$*$: & (R,\%) $\to$ \% & left multiplication by a scalar\\
$*$: & (\%,R) $\to$ \% & right multiplication by a scalar\\
+: & (\%,\%) $\to$ \% & addition of two vectors\\
-: & (\%,\%) $\to$ \% & substraction of two vectors\\
-: & \% $\to$ \% & additive inverse of a vector\\
\#: & \% $\to$ SI & dimension of a vector\\
add!: & (\%,\%) $\to$ \% & in-place addition of two vectors\\
apply: & (\%,SI) $\to$ R & to select a vector element\\
coerce: & \% $\to$ List R & returns a list of the elements in the vector\\
copy: & \% $\to$ \% & get a copy of a vector\\
map!: & (R$\to$R,\%) $\to$ \% & in-place mapping of a function onto a vector\\
minus!: & \% $\to$ \% & in-place additive inverse of a vector\\
new: & (SI,R) $\to$ \% & to get a new vector\\
random: & SI $\to$ \% & returns a randomly generated vector\\
set!: & (\%,SI,R) $\to$ R & to modify a vector element\\
subtract!: & (\%,\%) $\to$ \% & in-place subtraction\\
tensor: & (\%, \%) $\to$ \% & tensor product\\
times!: & (R,\%) $\to$ \% & in-place left multiplication by a scalar\\ 
times!: & (\%,R) $\to$ \% & in-place right multiplication by a scalar\\ 
vector: & List R $\to$ \% & build a vector form a list of elements\\
zero: & SI $\to$ \% & build a zero vector\\
zero?: & \% $\to$ Boolean & test for a zero vector\\
\end{exports}
\Aswhere{
SI &==& SingleInteger\\
}
#endif

Vector (R:SumitRing) : SumitType with
{
     *:             (R,%)     -> %;
     *:             (%,R)     -> %;
#if ASDOC
\aspage{$*$}
\begin{usage}
r~\name~v\\
v~\name~r
\end{usage}
\Signatures{
\name: & (R,\%) $\to$ \%\\
\name: & (\%,R) $\to$ \%
}
\Params{
{\em r} & R & An element of the coefficient ring.\\
{\em v} & \% & A vector with coefficients from R.\\
}
\Descr   {Multiplication of a vector by a scalar.}
\seealso {times!(\this)}
#endif
     +:             (%,%)     -> %;
#if ASDOC
\aspage    {+}
\Usage     {u~\name~v}
\Signature {(\%,\%)}{\%}
\Params    {{\em u}, {\em v} & \% & Vectors with coefficients from R.}
\Descr     {Addition of two vectors.}
\seealso   {add!(\this)}
#endif
     -:             (%,%)     -> %;
#if ASDOC
\aspage    {-}
\Usage     {u~\name~v}
\Signature {(\%,\%)}{\%}
\Params    {{\em u}, {\em v} & \% & Vectors with coefficients from R.}
\Descr     {substraction of two vectors.}
\seealso   {subtract!(\this)}
#endif
     -:             %         -> %;
#if ASDOC
\aspage    {-}
\Usage     {\name~v}
\Signature {\%}{\%}
\Params    {{\em v} & \% & A vector with coefficients from R.}
\Descr     {additive inverse of a vector. $v$ is destroyed.}
\seealso   {minus!(\this)}
#endif
     #:             %         -> SI;
#if ASDOC
\aspage    {\#}
\Usage     {\name~v}
\Signature {\%}{SI}
\Params    {{\em v} & \% & A vector with coefficients from R.}
\Descr     {dimension of vector $v$.}
#endif
     add!:          (%,%)     -> %;
#if ASDOC
\aspage    {add!}
\Usage     {\name(u,v)}
\Signature {(\%,\%)}{\%}
\Params    {{\em u}, {\em v} & \% & Vectors with coefficients from R.}
\Descr     {In-place addition of two vectors. $u$ is destroyed.}
#endif
     apply:         (%,SI)    -> R;
#if ASDOC
\aspage    {apply}
\Usage     {\name(v,i)}
\Signature {(\%,SI)}{R}
\Params    {{\em v} & \% & A vector with coefficients from R.\\
            {\em i} & SI & An indice.\\}
\Retval    {$v_i$}
#endif
     coerce:        %         -> List R;
#if ASDOC
\aspage    {coerce}
\Usage     {\name~v}
\Signature {\%}{List R}
\Params    {{\em v} & \% & A Vector with coefficients from R.}
\Descr     {coerce a vector, $v$, into a list, $l$, such that
             $l(i) = v_i, i=1,\ldots,\#v$.}
#endif
     copy:          %         -> %;
#if ASDOC
\aspage    {copy}
\Usage     {\name~v}
\Signature {\%}{\%}
\Params    {{\em v} & \% & A vector with coefficients from R.}
\Retval    {an independant copy of vector $v$.}
#endif
     map!:          (R->R,%)  -> %;
#if ASDOC
\aspage    {map!}
\Usage     {\name~(f,v)}
\Signature {(R$\to$R,\%)}{\%}
\Params    {{\em v} & \% & A vector with coefficients from R. \\
            {\em f} & R $\to$ R & any function.}
\Retval    {apply function $f$ to every element in $v$ (in-place).}
#endif
     minus!:        %         -> %;
#if ASDOC
\aspage    {minus!}
\Usage     {\name~v}
\Signature {\%}{\%}
\Params    {{\em v} & \% & A vector with coefficients from R.}
\Descr     {in-place additive inverse of a vector. $u$ is destroyed.}
#endif
     new:           (SI,R)    -> %;
#if ASDOC
\aspage    {new}
\Usage     {\name(n,r)}
\Signature {\%}{\%}
\Params    {{\em n} & SI & The dimension of the new vector.\\
            {\em r} & R  & The value to fill the vector with.\\}
\Retval    {a new $n$ dimensional vector filled with value $r$}
#endif
     random:        SI        -> %;
#if ASDOC
\aspage    {random}
\Usage     {\name~n}
\Signature {SI}{\%}
\Params    {{\em n} & SI & The dimension of the new vector.}
\Retval    {a new random $n$ dimensional vector.}
#endif
     set!:          (%,SI,R)  -> R;
#if ASDOC
\aspage    {set!}
\Usage     {\name(v,i,r)}
\Signature {(\%,SI,R)}{R}
\Params    {{\em v} & \% & A vector with coefficients from R.\\
            {\em i} & SI & An indice. \\
            {\em r} & R & an element of the ring \\}
\Descr     {$v_i \gets r$}
#endif
     substract!:    (%,%)     -> %;
#if ASDOC
\aspage    {substract!}
\Usage     {\name(u,v)}
\Signature {(\%,\%)}{\%}
\Params    {{\em u}, {\em v} & \% & Vectors with coefficients from R.}
\Descr     {in-place substraction of two vectors.}
#endif
	tensor:	(%, %) -> %;
#if ASDOC
\aspage{tensor}
\Usage{\name(u,v)}
\Signature{(\%,\%)}{\%}
\Params{{\em u}, {\em v} & \% & Vectors with coefficients from R.}
\Retval{Returns
$u \otimes v = (u_1 v_1, u_1 v_2, \dots, u_1 v_m, u_2 v_1, \dots, u_n v_m)$.}
#endif
     times!:        (R,%)     -> %;
     times!:        (%,R)     -> %;
#if ASDOC
\aspage{times!}
\begin{usage}
\name(r,v)\\
\name(v,r)
\end{usage}
\Signatures{
\name: & (R,\%) $\to$ \%\\
\name: & (\%,R) $\to$ \%
}
\Params{
{\em r} & R & An element of the coefficient ring.\\
{\em v} & \% & A vector with coefficients from R.\\
}
\Descr   {in-place multiplication of a vector by a scalar. $v$ is destroyed.}
#endif
     vector:        List R    -> %;
#if ASDOC
\aspage    {vector}
\Usage     {\name~l}
\Signature {List R}{\%}
\Params    {{\em l} & List R & A list of elements from R.}
\Descr     {create a new vector from a list}
\Retval    {$v$, a $\#l$ dimensional vector with $v_i = l_i, i=1,\ldots,\#l$.}
#endif
     zero:          SI        -> %;
#if ASDOC
\aspage    {zero}
\Usage     {\name~n}
\Signature {SI}{\%}
\Params    {{\em n} & SI & The dimension of the new vector.\\}
\Retval    {a new zero $n$ dimensional vector}
#endif
     zero?:         %         -> Boolean;
#if ASDOC
\aspage    {zero?}
\Usage     {\name~v}
\Signature {\%}{Boolean}
\Params    {{\em v} & \% & A vector with coefficients from R.\\}
\Retval    {test for the zero vector.}
#endif
}
== add
{
     macro ARR == PrimitiveArray R;
     macro Rep == Record( nbelement:SI, primarr:ARR );
     import from ARR,Rep;

     -- Internal macro to get the primitive array;
     macro pa(v) == rep(v).primarr;

     (u:%) = (v:%) : Boolean ==
     {
          #u ~= #v => false;
          for i in 1..#u repeat pa(u).i ~= pa(v).i => return false;
          true;
     }

     (p:TextWriter) << (v:%) : TextWriter == tex(p,extree v)$ExpressionTree;

     (r:R) * (v:%) : % == times!(r,copy v);
     (v:%) * (r:R) : % == times!(copy v,r);
     (u:%) + (v:%) : % == add!(copy u,v);
     (u:%) - (v:%) : % == substract!(copy u,v);
           - (v:%) : % == minus!(copy v);

     # (v:%) : SI == rep(v).nbelement;

     add! (u:%,v:%) : % ==
     {
          ASSERT(#u=#v);
          for i in 1..#v repeat pa(u).i := pa(u).i + pa(v).i;
          u;
     }

     apply (v:%,i:SI) : R ==
     {
          ASSERT(0<i);
          ASSERT(i<=#v);
          pa(v).i;
     }

     coerce (v:%) : List R == [ pa(v).i for i in 1..#v ];

     copy (v:%) : % == 
     {
          pau:ARR := new(#v);
          for i in 1..#v repeat pau.i := pa(v).i;
          per [#v,pau];
     }

     extree (v:%) : ExpressionTree ==
     {
          import from List ExpressionTree;
          ExpressionTreeVector(
               cons( extree(leaf(#v)$ExpressionTreeLeaf), 
                  [ (extree(pa(v).i)) for i in 1..#v ] )
          );
     }

     map! (f:R->R, v:%) : % == 
     {
          for i in 1..#v repeat pa(v).i := f(pa(v).i); 
          v;
     }

     minus! (v:%) : % ==
     {
          for i in 1..#v repeat pa(v).i := -pa(v).i;
          v;
     }

     new (n:SI,r:R) : % == per [n,new(n,r)];

     random (n:SI) : % == 
     {
          pau:ARR := new(n);
          for i in 1..n repeat
               pau.i := (randomInteger()$RandomNumberGenerator)::R;
          per [n,pau];
     }

     sample: % == zero 1;

     set! (v:%,i:SI,r:R) : R ==
     {
          ASSERT(i>0);
          ASSERT(i<=#v);
          pa(v).i := r;      
     }

     substract! (u:%,v:%) : % ==
     {
          ASSERT(#u=#v);
          for i in 1..#v repeat pa(u).i := pa(u).i - pa(v).i;
          u;
     }

	tensor(u:%, v:%):% == {
		n := #u; pu := pa u;
		m := #v; pv := pa v;
		w:ARR := new(nm := n * m);
		k:SI := 1;
		for i in 1..n repeat for j in 1..m repeat {
			w.k := pu.i * pv.j;
			k := next k;
		}
		per [nm, w];
	}

     times! (r:R,v:%) : % ==
     {
          for i in 1..#v repeat pa(v).i := r * pa(v).i;
          v;
     }

     times! (v:%,r:R) : % ==
     {
          for i in 1..#v repeat pa(v).i := pa(v).i * r;
          v;
     }

     -- Internal function to build a vector
     vector( n:SI, v:ARR ) : % == per [n,v ];

     vector( l:List R ) : % ==
     {
          pau:ARR := new(#l);
          for i in 1..#l  for r in l repeat pau.i := r;
          per [#l,pau];
     }

     zero( n:SI ) : % == per [n,new(n,0$R)];

     zero? (v:%) : Boolean ==
     {
          for i in 1..#v repeat pa(v).i ~= 0 => return false;
          true;
     }
}

#if SUMITTEST
---------------------- test vect.as --------------------------
#include "sumittest.as"

inplace():Boolean ==
{
     macro R == Integer;
     macro V == Vector R;
     import from R,V,List R;

     u := vector [1,2,3,4,5,6];
     v := vector [6,5,4,3,2,1];
     w := vector [1,1,1,1,1,1];
     t := copy u;

     w := times!(7,w);
     u := add!(u,v);
     u ~= w => false;
     u := substract!(u,v);
     u ~= t => false;
     zero? add!( t, minus!(u) );
}

print << "Testing vect..." << newline;
sumitTest("in-place operations", inplace);
print << newline;
#endif
