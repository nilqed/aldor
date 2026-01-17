# The Aldor Programming Language

### scan-build

```
clang version 18.1.8 
Thu Jan 15 22:38:56 2026
```

[scan-build report (HTML)](https://nilqed.github.io/aldor-scan-build/)


### gdb

Use `gdb -p <pid>` of running `aldor -g loop` process in `libexec`
(`ps xa | grep aldor`).


```
kfp@omega:~$ sudo gdb -p 879480
[sudo] password for kfp:
GNU gdb (Ubuntu 15.0.50.20240403-0ubuntu1) 15.0.50.20240403-git
Copyright (C) 2024 Free Software Foundation, Inc.
License GPLv3+: GNU GPL version 3 or later <http://gnu.org/licenses/gpl.html>

(gdb) run -g loop
Starting program: /usr/local/libexec/aldor -g loop
[Thread debugging using libthread_db enabled]
Using host libthread_db library "/lib/x86_64-linux-gnu/libthread_db.so.1".
warning: could not find '.gnu_debugaltlink' file for /lib/x86_64-linux-gnu/libtinfo.so.6
Aldor

Copyright (c) 1990-2007 Aldor Software Organization Ltd (Aldor.org).

Release: Aldor(C) version 1.4.0(2c53e759f1e00e345f8b172e7139debda72fda13) for LINUX(glibc2.10+) (debug version)
Type "#int help" for more details.
[1] -> #int history on
%%2 := 2
^
[L2 C1] #1 (Error) No meaning for integer-style literal `2'.

%%3 := %2
^
[L3 C1] #1 (Error) No meaning for identifier `%2'.

%%4 := %344
^
[L4 C1] #1 (Error) No meaning for identifier `%344'.

%%5 := #include "aldor"
                                           Comp: 50 msec, Interp: 0 msec
%%6 := #include "aldorinterp"
                                           Comp: 20 msec, Interp: 0 msec
%%7 := 2
^
[L7 C1] #1 (Error) No meaning for integer-style literal `2'.

%%8 := import from Integer
                                           Comp: 10 msec, Interp: 0 msec
%%9 := 2

Program received signal SIGSEGV, Segmentation fault.
0x0000555555705da7 in dnfIsTrue (xx=0x0) at dnf.c:391
391             return xx->argc == 1 && dnfAndIsTrue(xx->argv[0]);
(gdb)
(gdb) next
compSignalHandler (signo=0) at axlcomp.c:1378
1378    {
(gdb) next
1383            if      (signo == SIGFAKE)      sigerr = ALDOR_E_SigUnknown;
(gdb) next
1384            else if (signo == SIGHUP)       sigerr = ALDOR_E_SigHup;
(gdb) next
1385            else if (signo == SIGINT)       sigerr = ALDOR_E_SigInt;
(gdb) next
1386            else if (signo == SIGQUIT)      sigerr = ALDOR_E_SigQuit;
(gdb) next
1387            else if (signo == SIGILL)       sigerr = ALDOR_E_SigIll;
(gdb) next
1388            else if (signo == SIGTRAP)      sigerr = ALDOR_E_SigTrap;
(gdb) next
1389            else if (signo == SIGABRT)      sigerr = ALDOR_E_SigAbrt;
(gdb) next
1390            else if (signo == SIGEMT)       sigerr = ALDOR_E_SigEmt;
(gdb) next
1391            else if (signo == SIGFPE)       sigerr = ALDOR_E_SigFpe;
(gdb) next
1392            else if (signo == SIGBUS)       sigerr = ALDOR_E_SigBus;
(gdb) next
1393            else if (signo == SIGSEGV)      sigerr = ALDOR_E_SigSegv;
(gdb) next
1402            osDisplayMessage(comsgString(sigerr));
(gdb) next
1403            comsgError(NULL, sigerr, signo);
(gdb) next
Program fault (segmentation violation).#1 (Error) Program fault (segmentation violation).
1404            fflush(dbOut);
(gdb) next
1405            exitFailure();
(gdb) next
[Inferior 1 (process 879642) exited with code 01]
(gdb) next
The program is not being run.
(gdb) next
The program is not being run.
(gdb)
```  

### Additional Interpreter Options

We may set the standard prompt or the history[on] prompt as below:

```
kfp@omega:~/quicklisp/local-projects/aldor/aldor/test$ aldor -g loop
Aldor

Copyright (c) 1990-2007 Aldor Software Organization Ltd (Aldor.org).

Release: Aldor(C) version 1.4.0(2c53e759f1e00e345f8b172e7139debda72fda13) for LINUX(glibc2.10+) (debug version)
Type "#int help" for more details.
Reading aldorinit.as...
                                           Comp: 30 msec, Interp: 10 msec
                                           Comp: 30 msec, Interp: 0 msec
                                           Comp: 0 msec, Interp: 0 msec
                                           Comp: 10 msec, Interp: 0 msec
                                           Comp: 0 msec, Interp: 0 msec
                                           Comp: 0 msec, Interp: 0 msec
%%8 >> #int help

Available options:

#int verbose [on|off]  print the value of an evaluated expression.
#int history [on|off]  try to wrap an assignment around the current line.
#int confirm [on|off]  ask for confirmation before redefining something.
#int timing [on|off]  display timings after every input.
#int msg-limit [num]  set the limit size of some messages; 0 for no-limit.
#int options ...  reset command line options.
#int gc     perform garbage collection.
#int shell "<command>"  execute a shell command.
#int cd <directory>  change current directory.
#int exntrace [0|1|2]  display backtrace when an exception occurs.
     0: never, 1: only when not caught, 2: always.
#int set-sprompt "<fmt-string>"  set standard prompt.
#int set-hprompt "<fmt-string>"  set history prompt.
#int set-typefmt "<fmt-string>"  set type output format.
#int help     display this message.

#quit       quit the interactive loop.
%%9 >> #int set-sprompt "[%d] -> "
[10] -> #int set-hprompt "(%d) -> "
[11] ->
[11] -> #int history on
(12) -> 23
23 @ AldorInteger
                                           Comp: 0 msec, Interp: 30 msec
(13) -> %23
^
[L17 C1] #1 (Error) No meaning for identifier `%23'.

(14) -> %12
23 @ AldorInteger
                                           Comp: 0 msec, Interp: 0 msec
(15) ->
```

#### Howto: 

 1. Declare variables in `fintphase.c`
 2. Import extern in `axlcomp.c` (if necessary)
 3. Add `FINT_DECLARE_OPTION` in `fintphase.c`
 4. Add handler there (below)
 5. Don't forget to add `<x>OPt` to the `helpOpt` list!
 6. Add new `ALDOR_M_xxx` in `comsgdb.msg`
 7. Add corresponding `#int %s ...` entry at the correct position in `comsgdb.msg`
 

Printing `types` is still tricky. We have to use `$` for the `\\n` character,
because of the filtering in the `scmdScanFName` function (?). An example of
a type format string is given below:

```
%%8 >> 4
4 @ AldorInteger
                                           Comp: 0 msec, Interp: 20 msec
%%9 >> #int set-typefmt "$ $Type: %s $"
%%10 >> 4
4

Type: AldorInteger
                                           Comp: 0 msec, Interp: 0 msec
                                           
todo:
#int set-typefmt "$ $Type: %20s $"   -- right justify 
```
---





---

Choose the master branch or switch to the original 
https://github.com/aldorlang/aldor for cloning/building. 


Docs in various formats: http://nilqed.github.io/aldor/


