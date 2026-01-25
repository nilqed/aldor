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
------------------------------- sal_timer.as ----------------------------------
--
-- This file provides a stopwatch-style timers for code profiling
--
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-97
-- Copyright (c) Manuel Bronstein 1994-98
-- Copyright (c) INRIA 1998, Version 29-10-98
-- Logiciel Salli ©INRIA 1998, dans sa version du 29/10/1998
-----------------------------------------------------------------------------

#include "salli"

#if ALDOC
\thistype{Timer}
\History{Manuel Bronstein}{22/5/94}{created}
\History{Manuel Bronstein}{1/10/98}{moved from sumit to salli and adapted}
\Usage{import from \this}
\Descr{\this~is a type whose elements are stopwatch timers, which can be used
to time precisely various sections of code, including garbage collection.
The precision can be up to 1 millisecond but depends on the operating system.
The times returned are CPU times (user + gc) used by the process that
created the timer.}
\begin{exports}
\asexp{gc}:     & \%  $\to$ \astype{MachineInteger} & read a timer\\
\asexp{read}:   & \%  $\to$ \astype{MachineInteger} & read a timer\\
\asexp{reset!}: & \%  $\to$ \% & reset a timer to 0\\
\asexp{start!}: & \%  $\to$ \astype{MachineInteger} & start or restart a timer\\
\asexp{stop!}:  & \%  $\to$ \astype{MachineInteger} & stop a timer\\
\asexp{timer}:  & () $\to$ \% & create a new timer\\
\end{exports}
#endif

macro Z == MachineInteger;

Timer: with {
	gc: % -> Z;
#if ALDOC
\aspage{gc}
\Signature{\%}{\astype{MachineInteger}}
\Params{ {\em t} & \% & The timer to read\\ }
\Descr{Reads the timer t without stopping it.}
\Retval{Returns the total accumulated garbage collection time in
milliseconds by all
the start/stop cycles since t was created or last reset.
If t is running, the garbage collection time since the last start is added in,
and t is not stopped or affected.}
\seealso{\asexp{read}}
#endif
	read:   %  -> Z;
#if ALDOC
\aspage{read}
\Usage{\name~t}
\Signature{\%}{\astype{MachineInteger}}
\Params{ {\em t} & \% & The timer to read\\ }
\Descr{Reads the timer t without stopping it.}
\Retval{Returns the total accumulated time in milliseconds by all
the start/stop cycles since t was created or last reset.
This times includes any eventual garbage collection time
(see \asexp{gc} to extract this information).
If t is running, the time since the last start is added in,
and t is not stopped or affected.}
\begin{asex}
The following function takes a positive \astype{MachineInteger} $n$ as input,
computes and prints a machine approximation of $\sum_{i=1}^n 1/i$,
and returns the CPU time needed to compute it,
but not the time needed to print it.
\begin{ttyout}
timeHarmonic(n:MachineInteger):MachineInteger == {
        import from MachineInteger, SingleFloat, Timer, Character, TextWriter;
        t := timer();
        m:SingleFloat := 1;
        start! t;
        for i in 2..n repeat m := m + 1 / (i::SingleFloat);
        stop! t;
        stdout << "H" << n << " = " << m << newline;
        read t;
}
\end{ttyout}
\end{asex}
\seealso{\asexp{gc}, \asexp{start!}, \asexp{stop!}}
#endif
	reset!: %  -> %;
#if ALDOC
\aspage{reset!}
\Usage{\name~t}
\Signature{\%}{\%}
\Params{ {\em t} & \% & The timer to reset\\ }
\Descr{Resets the timer t to 0 and stops it if it is running.}
\Retval{Returns the timer t after it is reset.}
#endif
	start!: %  -> Z;
#if ALDOC
\aspage{start!}
\Usage{\name~t}
\Signature{\%}{\astype{MachineInteger}}
\Params{ {\em t} & \% & The timer to start\\ }
\Descr{Starts or restarts t, without resetting it to 0,
It has no effect on t if it is already running.}
\Retval{Returns 0 if t was already running, the absolute time at which
the start/restart was done otherwise.}
\seealso{\asexp{read}, \asexp{stop!}}
#endif
	stop!:  %  -> Z;
#if ALDOC
\aspage{stop!}
\Usage{\name~t}
\Signature{\%}{\astype{MachineInteger}}
\Params{ {\em t} & \% & The timer to stop\\ }
\Descr{Stops t without resetting it to 0.
It has no effect on t if it is not running.}
\Retval{Returns the elapsed time in milliseconds since the last time t
was restarted, 0 if t was not running.}
\seealso{\asexp{read}, \asexp{start!}}
#endif
	timer:  () -> %;
#if ALDOC
\aspage{timer}
\Usage{\name()}
\Signature{()}{\%}
\Descr{Creates a timer, set to 0 and stopped.}
\Retval{Returns the timer that has been created.}
\seealso{\asexp{reset!}}
#endif
} == add {
        -- time     = total accumulated time since created or reset
        -- start    = absolute time of last start
        -- gctime   = total accumulated GC-time since created or reset
        -- gcstart  = absolute GC-time of last start
        -- running? = true if currently running, false if currently stopped
	Rep == Record(time:Z,start:Z,gctime:Z,gcstart:Z,running?:Boolean);

	local start(t:%):Z		== { import from Rep; rep(t).start; }
	local gcstart(t:%):Z		== { import from Rep; rep(t).gcstart; }
	local time(t:%):Z		== { import from Rep; rep(t).time; }
	local gctime(t:%):Z		== { import from Rep; rep(t).gctime; }
	local running?(t:%):Boolean	== { import from Rep; rep(t).running?; }

	timer():% == {
		import from Rep, Z, Boolean;
		per [0, 0, 0, 0, false];
	}

	local gcTime():Z == {
		import { gcTimer: () -> Pointer } from Foreign C;
		import from Record(gc:Z);
		(gcTimer() pretend Record(gc:Z)).gc;
	}

	local cpuTime():Z == {
		import { osCpuTime: () -> Z } from Foreign C;
		osCpuTime();
	}

	gc(t:%):Z == {
		running? t => gctime t + gcTime() - gcstart t;
		gctime t;
	}

	read(t:%):Z == {
		running? t => time t + cpuTime() - start t;
		time t;
	}

	stop!(t:%):Z == {
		running? t =>
			stop!(rep t, cpuTime() - start t, gcTime() - gcstart t);
		0;
	}

	local stop!(r:Rep, elapsed:Z, gcelapsed:Z):Z == {
		import from Boolean;
		r.running? := false;
		r.time := r.time + elapsed;
		r.gctime := r.gctime + gcelapsed;
		elapsed;
	}

	start!(t:%):Z == {
		running? t => 0;
		start!(rep t, cpuTime(), gcTime());
	}

	local start!(r:Rep, time:Z, gctime:Z):Z == {
		r.start := time;
		r.gcstart := gctime;
		r.running? := true;
		time;
	}

	reset!(t:%):% == {
		import from Rep, Boolean;
		rec := rep t;
		rec.time := rec.start := rec.gcstart := 0;
		rec.running? := false;
		t
	}
}
