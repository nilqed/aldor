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
------------------------------sit_condif.as------------------------------
-- Copyright (c) Marco Codutti 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995
-----------------------------------------------------------------------------

#include "sumit"

macro {
	TREE == ExpressionTree;
	TEXT == TextWriter;
}

#if ALDOC
\thistype{If}
\History {Marco Codutti}{20 June 95}{created}
\Usage   {import from \this(C,O)}
\Params{
        {\em C} & \astype{Condition} & The kind of conditions\\
        {\em O} & \astype{SumitType} & The kind of objects \\
}
\Descr   {\this~implements a structure where a condition of type $C$ is 
          associated to an object of type $O$.}
\begin{exports}
\category{\astype{SumitType}}\\
\asexp{bracket}: & (C,O) $\to$ \% & build a conditional object \\
\asexp{coerce}:  & O $\to$ \% &
make an object with condition \asfunc{Condition}{Always}\\
\asexp{condition}: & \% $\to$ C & condition associated to an object\\
\asexp{\_if}: & (C,O) $\to$ \% & build a conditional object \\
\asexp{never?}: & \% $\to$ \astype{Boolean} &
test if it the condition is \asfunc{Condition}{Never}\\
\asexp{object}: & \% $\to$ O & object associated to a condition\\
\end{exports}
#endif

If(C:Condition, O:SumitType): SumitType with {
     bracket:      (C,O) -> %;
     _if:      (C,O) -> %;
#if ALDOC
\aspage    {bracket,\_if}
\astarget  {bracket}
\astarget  {\_if}
\Usage     {[c,o]\\ bracket(c,o)\\ \_if(c, o)}
\Signature {(C,O)}{\%}
\Params    { {\em c} & C & a condition \\
             {\em o} & O & an object\\
           }
\Retval    {Return a new conditional object where condition $c$ is associated
            to object $o$.}
#endif
     coerce:        O    -> %;
#if ALDOC
\aspage    {coerce}
\Usage     {a::If(C,O)\\ \name~a}
\Signature {O}{\%}
\Params    { {\em o} & O & an object\\ }
\Retval     {Retrun a new conditional object where the condition
	    \asfunc{Condition}{Always} is associated to object $o$.}
#endif
     condition:     %    -> C;
#if ALDOC
\aspage    {condition}
\Usage     {\name~a}
\Signature {\%}{C}
\Params    { {\em a} & \% & a conditional object \\ }
\Retval    {Return the condition of the conditional object $a$.}
#endif
     never?:   %    -> Boolean;
#if ALDOC
\aspage    {never?}
\Usage     {\name~a}
\Signature {\%}{\astype{Boolean}}
\Params    { {\em a} & \% & a conditional object \\ }
\Retval    {Return \true if the condition associated to $a$ is
           \asfunc{Condition}{Never}, \false otherwise.}
#endif
     object:        %    -> O;
#if ALDOC
\aspage    {object}
\Usage     {\name~a}
\Signature {\%}{O}
\Params    { {\em a} & \% & a conditional object \\ }
\Retval    {Return the object of the conditional object $a$.}
#endif
} == add {
     Rep == Record(condition:C, object:O);
     import from Rep;

     (c1:%) = (c2:%) : Boolean ==
          (condition c1 = condition c2) and (object c1 = object c2);

--     (p:TEXT) << (c:%)  : TEXT    == {
--          p << condition c << " ==> " << object c;
--     }

     bracket     (c:C,o:O) : %		== per [c, o];
     _if         (c:C,o:O) : %		== [c, o];
     coerce      (o:O)     : %		== [Always, o];
     condition   (c:%)     : C		== rep(c).condition;
     object      (c:%)     : O		== rep(c).object;
     never?      (c:%)     : Boolean	== never? condition c;

     extree (c:%) : TREE == {
          import from TREE, List TREE;
          ExpressionTreeIf [ extree condition c, extree object c ];
    }
}

