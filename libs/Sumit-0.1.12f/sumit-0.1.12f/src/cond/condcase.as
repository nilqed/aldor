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
------------------------------   condcase.as   ------------------------------
#include "sumit.as"

macro TREE == ExpressionTree;
macro TEXT == TextWriter;

#if ASDOC
\thistype{Case}
\History {Marco Codutti}{20 June 95}{created}
\Usage   {import from \this(C,O)}
\Params{
        {\em C} & ConditionCategory & The kind of conditions\\
        {\em O} & SumitType & The kind of objects \\
}
\Descr   {\this~is a set of If(C,O).}
\begin{exports}
\category{SumitType}\\
\category{FiniteLinearAggregate IF}\\
addNewCase!: & (\%,IF) $\to$ \% & In-place add a new case.\\
coerce:      & IF      $\to$ \% & natural embedding.\\
join!:       & (\%,\%) $\to$ \% & In-place join.\\  
\end{exports}
\Aswhere{ IF &==& If(C,O) \\ }
#endif

macro IF == If(C,O);
Case(C:ConditionCategory, O:SumitType):
     Join( SumitType, FiniteLinearAggregate IF) with
{
     addNewCase!:   (%,IF) -> %;
#if ASDOC
\aspage    {addNewcase!}
\Usage     {\name~(a,c)}
\Signature {IF}{\%}
\Params    { {\em a} & \% & a set of conditional object\\
             {\em c} & IF & a conditional object.\\
           }
\Descr     {add $c$ to set $a$ (in-place).
            $c$ is not added if its condition is {\em never}.}
#endif
     case:        Tuple IF     -> %;
#if ASDOC
\aspage    {case}
\Usage     {\name~a}
\Signature {Tuple IF}{\%}
\Params    { {\em a} & IF & a tuple of conditional objects\\
           }
\Descr     {Create a new case structure from a tuple of conditional objects.}
#endif
     coerce:        IF     -> %;
#if ASDOC
\aspage    {coerce}
\Usage     {\name~c}
\Signature {IF}{\%}
\Params    { {\em c} & IF & a conditional object\\
           }
\Descr     {Natural embedding. Returns $c$ as a one-element set of conditional
            objects}
#endif
     join!:         (%,%)  -> %;
#if ASDOC
\aspage    {Join!}
\Usage     {\name~(a,b)}
\Signature {IF}{\%}
\Params    { {\em a}, {\em b} & \% & two sets of conditional object\\
           }
\Descr     {join two sets of conditional object together.
            In-place operation, $a$ is destroyed.}
#endif
}
== add
{
     macro Rep == List IF;
     import from Rep;

     (c1:%) = (c2:%) : Boolean == {
          (#c1 ~= #c2)$SingleInteger => false;
          for cas in c1 repeat ~member?(cas,rep c2) => return false;
          true;
     }

--     (p:TEXT) << (c:%)  : TEXT == {
--          import from SingleInteger;
--          p << "Case:" << newline;
--          for i in 1..#c for cas in c repeat
--               p << "  " << i << ": " << cas << newline;
--          p;
--     }
 
     # (m:%) : SingleInteger == #(rep m);

     addNewCase! (m:%,c:IF) : % == 
          if degenerate? c then m else per cons(c,rep m);

     apply   (m:%,i:SingleInteger) : IF == rep(m).i;
     bracket (g:Generator(IF))     : %  == per [g];
     bracket (t:Tuple(IF))         : %  == per [t];
     case    (t:Tuple(IF))         : %  == per [t];
     coerce  (c:IF)                : %  == per [c];
 
     extree (c:%) : TREE ==
     {
          import from TREE, List TREE, O, C;
          l := empty()$List(TREE);
          for cas in rep(c) repeat
          {
               l := cons(extree object    cas, l);
               l := cons(extree condition cas, l);
          }
          ExpressionTreeCase reverse! l;
     }

     generator (m:%) : Generator IF == generator rep m;

     join! (m1:%,m2:%) : % ==
     {
          res := m1;
          for cas in m2 repeat res := addNewCase!(res,cas);
          res; 
     }

     sample: % == per [sample];
}
