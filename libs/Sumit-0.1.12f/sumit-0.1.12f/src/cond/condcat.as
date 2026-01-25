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
------------------------------   condcat.as   ------------------------------
#include "sumit.as"

#if ASDOC
\thistype{ConditionCategory}
\History {Marco Codutti}{14 June 95}{created}
\Usage   {\this: Category}
\Descr   {\this~is a category for conditions on parameters.}
\begin{exports}
\category{SumitType}\\
\category{Logic}\\
Always: & () $\to$ \%      & a condition which is always satisfied \\
always?:  & \% $\to$ Boolean & test is a condition is {\em always}\\
and!:     & (\%,\%) $\to$ \% & in-place logical and\\
copy:     & \% $\to$ \%      & take a copy of a condition\\
Never:  & () $\to$ \%      & a condition which is never satisfied \\
never?:   & \% $\to$ Boolean & test is a condition is {\em never}\\
\end{exports}
#endif

ConditionCategory : Category == Join(SumitType,Logic) with 
{
     Always: () -> %;
#if ASDOC
\aspage    {Always}
\Usage     {\name()}
\Signature {()}{\%}
\Retval    {a condition which is always satisfied.}
\Remarks   {the signature of this function should be {\em \name : \%}
            but it does'nt work in this release.
            It's name should be {\tt always} but it is a reserved token
            of the A\# language.}
#endif
     always?:%     -> Boolean;
#if ASDOC
\aspage    {always?}
\Usage     {\name~c}
\Signature {\%}{Boolean}
\Params    {{\em c} & \% & a condition}
\Descr     {test if $c$ is {\em always}}
#endif
     and!:   (%,%) -> %;
#if ASDOC
\aspage    {and!}
\Usage     {\name(a,b)}
\Signature {(\%,\%)}{\%}
\Params    {{\em a}, {\em b} & \% & conditions}
\Descr     {in-place logical and between $a$ and $b$. $a$ is destroyed.}
#endif
     copy:   %     -> %;
#if ASDOC
\aspage    {copy}
\Usage     {\name~c}
\Signature {\%}{\%}
\Params    {{\em c} & \% & a condition}
\Retval    {an independent copy of $c$.}
#endif
     Never:  () -> %;
#if ASDOC
\aspage    {Never}
\Usage     {\name()}
\Signature {()}{\%}
\Retval    {a condition which is never satisfied.}
\Remarks   {the signature of this function should be {\em \name : \%}
            but it does'nt work in this release.
            It's name should be {\tt never} but it is a reserved token
            of the A\# language
            }
#endif
     never?: %     -> Boolean;
#if ASDOC
\aspage    {never?}
\Usage     {\name~c}
\Signature {\%}{Boolean}
\Params    {{\em c} & \% & a condition}
\Descr     {test if $c$ is {\em never}}
#endif
}

