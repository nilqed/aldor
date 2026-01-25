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
------------------------------sit_condcas.as------------------------------
-- Copyright (c) Marco Codutti 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995
-----------------------------------------------------------------------------

#include "sumit"

macro {
	TREE == ExpressionTree;
	TEXT == TextWriter;
	IF == If(C,O);
	I == MachineInteger;
}

#if ALDOC
\thistype{Case}
\History {Marco Codutti}{20 June 95}{created}
\Usage   {import from \this(C,O)}
\Params{
        {\em C} & \astype{Condition} & The kind of conditions\\
        {\em O} & \astype{SumitType} & The kind of objects \\
}
\Descr   {\this~is a set of If(C,O).}
\begin{exports}
\category{\astype{BoundedFiniteLinearStructureType} \astype{If}(C,O)}\\
\category{\astype{SumitType}}\\
\asexp{addNewCase!}:
& (\%,\astype{If}(C,O)) $\to$ \% & In--place add a new case\\
\asexp{coerce}:      & \astype{If}(C,O)      $\to$ \% & Make a single case\\
\asexp{join!}:       & (\%,\%) $\to$ \% & In--place join\\  
\end{exports}
#endif

Case(C:Condition, O:SumitType):
	Join(SumitType, BoundedFiniteLinearStructureType IF) with {
	addNewCase!:   (%, IF) -> %;
#if ALDOC
\aspage    {addNewcase!}
\Usage     {\name~(a,c)}
\Signature {\astype{If}(C,O)}{\%}
\Params    { {\em a} & \% & a set of conditional objects\\
             {\em c} & \astype{If}(C,O) & a conditional object.\\
           }
\Descr     {Add $c$ to set $a$ (in--place).
            $c$ is not added if its condition is \asfunc{Condition}{Never}.}
#endif
	coerce:        IF     -> %;
#if ALDOC
\aspage    {coerce}
\Usage     {c::Case(C,O)\\ \name~c}
\Signature {\astype{If}(C,O)}{\%}
\Params    { {\em c} & \astype{If}(C,O) & a conditional object\\ }
\Retval    {Return $c$ as a one--element set of conditional objects}
#endif
	join!:         (%,%)  -> %;
#if ALDOC
\aspage    {join!}
\Usage     {\name~(a,b)}
\Signature {\astype{If}(C,O)}{\%}
\Params    { {\em a, b} & \% & sets of conditional objects\\ }
\Descr     {Join two sets of conditional object together.
            In--place operation, $a$ is destroyed.}
#endif
} == add {
     Rep == Set IF;
     import from Rep;

	(c1:%) = (c2:%):Boolean 	== rep(c1) = rep(c2);
	#(m:%):I			== #(rep m);
	apply(m:%, i:I):IF		== rep(m).i;
	bracket(g:Generator IF):%	== filter! per [g];
	bracket(t:Tuple IF):%		== filter! per [t];
	generator(m:%):Generator IF	== generator rep m;
	join!(m1:%, m2:%):%		== per union!(rep m1, rep m2);
	copy(m:%):%			== per copy rep m;
	(m:%) + (n:I):%			== per(rep(m) + n);
	firstIndex:I			== firstIndex$Rep;
	empty:%				== per empty;
	empty?(m:%):Boolean		== empty? rep m;
	free!(m:%):()			== free! rep m;
	new(n:I, c:IF):%		== per new(n, c);
	set!(m:%, n:I, c:IF):IF		== rep(m).n := c;
	map(f:IF -> IF)(m:%):%		== per(map(f)(rep m));
	map!(f:IF -> IF)(m:%):%		== per(map!(f)(rep m));

	if IF has SerializableType then {
		<< (p:BinaryReader):% == per(<< p);
	}

	if IF has InputType then {
		<< (p:TextReader):% == per(<< p);
	}

	local filter!(m:%):% == {
		import from IF;
		per minus!(rep m, [cas for cas in m | never? cas]);
	}

	find(c:IF, m:%):(%, I) == {
		(s, n) := find(c, rep m);
		(per s, n);
	}

--     (p:TEXT) << (c:%)  : TEXT == {
--          import from SingleInteger;
--          p << "Case:" << newline;
--          for i in 1..#c for cas in c repeat
--               p << "  " << i << ": " << cas << newline;
--          p;
--     }

	coerce(c:IF):% == {
		never? c => empty;
		[c];
	}

	addNewCase!(m:%, c:IF):% == {
		never? c => m;
		per union!(rep m, c);
	}
 
	extree(c:%):TREE == {
		import from List TREE, IF;
		ExpressionTreeCase [extree cas for cas in c];
	}
}
