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
------------------------------   condif.as   ------------------------------
#include "sumit.as"

macro TREE == ExpressionTree;
macro TEXT == TextWriter;

#if ASDOC
\thistype{If}
\History {Marco Codutti}{20 June 95}{created}
\Usage   {import from \this(C,O)}
\Params{
        {\em C} & ConditionCategory & The kind of conditions\\
        {\em O} & SumitType & The kind of objects \\
}
\Descr   {\this~implements a structure where a condition of type $C$ is 
          associated to an object of type $O$.}
\begin{exports}
\category{SumitType}\\
bracket: & (C,O) $\to$ \% & build a new conditional object \\
coerce:  & O     $\to$ \% & coerce to an object with condition {\em always}\\
condition: & \%  $\to$ C  & return the condition associated to an object\\
degenerate?: & \% $\to$ Boolean & tell if it is a degenerate conditional object\\
\_if: & (C,O) $\to$ \% & build a new conditional object \\
object: & \% $\to$ O & return the object to which a condition is associated\\
\end{exports}
#endif

If(C:ConditionCategory,O:SumitType): SumitType with
{
     bracket:      (C,O) -> %;
#if ASDOC
\aspage    {bracket}
\Usage     {\name~(c,o)}
\Signature {(C,O)}{\%}
\Params    { {\em c} & C & a condition \\
             {\em o} & O & an object\\
           }
\Descr     {Create a new conditional object where condition $c$ is associated
            to object $o$.}
#endif
     coerce:        O    -> %;
#if ASDOC
\aspage    {coerce}
\Usage     {\name~o}
\Signature {O}{\%}
\Params    { {\em o} & O & an object\\
           }
\Descr     {Create a new conditional object where condition {\em always}
           is associated to object $o$.}
#endif
     condition:     %    -> C;
#if ASDOC
\aspage    {condition}
\Usage     {\name~a}
\Signature {\%}{C}
\Params    { {\em a} & \% & a conditional object \\ }
\Descr     {return the condition of the conditional object $a$.}
#endif
     degenerate?:   %    -> Boolean;
#if ASDOC
\aspage    {degenerate?}
\Usage     {\name~a}
\Signature {\%}{Boolean}
\Params    { {\em a} & \% & a conditional object \\ }
\Descr     {check if the condition associated to $a$ is {\em never}}
#endif
     _if:      (C,O) -> %;
#if ASDOC
\aspage    {\_if}
\Usage     {\name~(c,o)}
\Signature {(C,O)}{\%}
\Params    { {\em c} & C & a condition \\
             {\em o} & O & an object\\
           }
\Descr     {Create a new conditional object where condition $c$ is associated
            to object $o$.}
#endif
     object:        %    -> O;
#if ASDOC
\aspage    {object}
\Usage     {\name~a}
\Signature {\%}{O}
\Params    { {\em a} & \% & a conditional object \\ }
\Descr     {return the object of the conditional object $a$.}
#endif
}
== add
{
     macro Rep == Record( condition:C, object:O );
     import from Rep;

     (c1:%) = (c2:%) : Boolean ==
          (condition c1 = condition c2) and (object c1 = object c2);

     (p:TEXT) << (c:%)  : TEXT    == {
          p << condition c << " ==> " << object c;
     }

     bracket     (c:C,o:O) : %       == per [c,o];
     coerce      (o:O)     : %       == [Always(),o];
     condition   (c:%)     : C       == rep(c).condition;
     degenerate? (c:%)     : Boolean == never? condition c;

-- We wait for basic objets (boolean,...) to be SumitType.
     extree (c:%) : TREE ==
     {
          import from TREE, List TREE;
          ExpressionTreeIf [ extree condition c, extree object c ];
    }

     _if    (c:C,o:O) : % == per [c,o];
     object (c:%)     : O == rep(c).object;
     sample           : % == [sample,sample];
}

