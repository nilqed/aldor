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
------------------------------- timer.as ----------------------------------
-- Copyright Manuel Bronstein, 1994-1998
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1994-97
-- Copyright INRIA, 1998

#include "sumit"

#if ASDOC
\thistype{Timer}
\History{Manuel Bronstein}{22/5/94}{created}
\Usage{import from \this}
\Descr{\this~is a type whose elements are stopwatch timers, which can be used
to time precisely various sections of code.
The precision can be up to 1 millisecond but depends on the operating system.
The times returned are CPU times used by the process that created the timer.}
\begin{exports}
timer:  & () $\to$ \% & create a new timer\\
start!: & \%  $\to$ Z & start or restart a timer\\
stop!:  & \%  $\to$ Z & stop a timer\\
read:   & \%  $\to$ Z & read a timer\\
reset!: & \%  $\to$ \% & reset a timer to 0\\
HMS:    & Z $\to$ (Z, Z, Z, Z) &
convert milliseconds to hours/minutes/seconds/millisecs\\
\end{exports}
\Aswhere{
Z &==& SingleInteger\\
}
#endif

macro Z == SingleInteger;

Timer: with {
	HMS:    Z -> (Z, Z, Z, Z);
#if ASDOC
\begin{aspage}{HMS}
\Usage{\name~n}
\Signature{SingleInteger}
{(SingleInteger,SingleInteger,SingleInteger,SingleInteger)}
\Params{ {\em n} & SingleInteger & The number of milliseconds to convert\\ }
\Retval{Returns (h, m, s, u) where n milliseconds is equal
to h hours, m minutes, s seconds and u milliseconds.}
\begin{asex}
\begin{ttyout}
import from {SingleInteger, Timer};
HMS(10^9);
\end{ttyout}
returns
\Asoutput{ \> (277,46,40,0) }
which means that $10^9$ milliseconds is equal to
277 hours, 46 minutes and 40 seconds.
\end{asex}
\end{aspage}
#endif
	read:   %  -> Z;
#if ASDOC
\begin{aspage}{read}
\Usage{\name~t}
\Signature{\this}{SingleInteger}
\Params{ {\em t} & \this & The timer to read\\ }
\Descr{Reads the timer t without stopping it.}
\Retval{Returns the total accumulated time in milliseconds by all
the start/stop cycles since t was created or last reset.
If t is running, the time since the last start is added in,
and t is not stopped or affected.}
\begin{asex}
The following function takes a positive SingleInteger $n$ as input,
computes adn prints $n!$, and returns the CPU time needed to compute it,
but not the time needed to print it.
\begin{ttyout}
timeFactorial(n:SingleInteger):SingleInteger == {
        import from {SingleInteger, Integer, Timer};
        t := timer();
        m:Integer := 1;
        start! t;
        for i in 2..n repeat m := (i::Integer) * m;
        stop! t;
        print << n << "! = " << m << newline;
        read t;
}
\end{ttyout}
\end{asex}
\seealso{start!(\this), stop!(\this)}
\end{aspage}
#endif
	reset!: %  -> %;
#if ASDOC
\begin{aspage}{reset!}
\Usage{\name~t}
\Signature{\this}{\this}
\Params{ {\em t} & \this & The timer to reset\\ }
\Descr{Resets the timer t to 0 and stops it if it is running.}
\Retval{Returns the timer t after it is reset.}
\end{aspage}
#endif
	start!: %  -> Z;
#if ASDOC
\begin{aspage}{start!}
\Usage{\name~t}
\Signature{\this}{SingleInteger}
\Params{ {\em t} & \this & The timer to start\\ }
\Descr{Starts or restarts t, without resetting it to 0,
It has no effect on t if it is already running.}
\Retval{Returns 0 if t was already running, the absolute time at which
the start/restart was done otherwise.}
\seealso{read(\this), stop!(\this)}
\end{aspage}
#endif
	stop!:  %  -> Z;
#if ASDOC
\begin{aspage}{stop!}
\Usage{\name~t}
\Signature{\this}{SingleInteger}
\Params{ {\em t} & \this & The timer to stop\\ }
\Descr{Stops t without resetting it to 0.
It has no effect on t if it is not running.}
\Retval{Returns the elapsed time in milliseconds since the last time t
was restarted, 0 if t was not running.}
\seealso{read(\this), start!(\this)}
\end{aspage}
#endif
	timer:  () -> %;
#if ASDOC
\begin{aspage}{timer}
\Usage{\name()}
\Signature{()}{\this}
\Descr{Creates a timer, set to 0 and stopped.}
\Retval{Returns the timer that has been created.}
\seealso{reset!(\this)}
\end{aspage}
#endif
} == add {
        -- time     = total accumulated time since created or reset
        -- start    = absolute time of last start
        -- running? = true if currently running, false if currently stopped
	Rep ==> Record(time:Z, start:Z, running?:Boolean);

	import from Rep, Z, Boolean, OperatingSystemInterface;

	timer():% == per [0, 0, false];

	read(t:%):Z == {
		rec := rep t;
		ans := rec.time;
		if rec.running? then ans := ans + cpuTime() - rec.start;
		ans
	}

	stop!(t:%):Z == {
		local ans:Z;
		rec := rep t;
		if rec.running? then {
			ans := cpuTime() - rec.start;
			rec.time := rec.time + ans;
			rec.running? := false
		}
		else ans := 0;
		ans
	}

	start!(t:%):Z == {
		local ans:Z;
		rec := rep t;
		if not(rec.running?) then {
			rec.start := ans := cpuTime();
			rec.running? := true;
		}
		else ans := 0;
		ans
	}

	reset!(t:%):% == {
		rec := rep t;
		rec.time := rec.start := 0;
		rec.running? := false;
		t
	}

	HMS(m:Z):(Z, Z, Z, Z) == {
		ASSERT(m >= 0);
		(h, m) := divide(m, 3600000);
		(m, s) := divide(m, 60000);
		(s, l) := divide(s, 1000);
		(h, m, s, l)
	}
}
