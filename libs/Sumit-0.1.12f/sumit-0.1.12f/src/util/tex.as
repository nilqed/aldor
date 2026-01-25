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
------------------------------- tex.as ----------------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1994
-- THIS FILE MUST BE COMPILED AND ARCHIVED FIRST

#include "salli"

#if ALDOC
\thistype{TeXEquation}
\History{Manuel Bronstein}{22/5/94}{created}
\Usage{import from \this~T}
\Params{ {\em T} & OutputType & A type whose linear output must be in \LaTeX }
\Descr{\this~provides functions for wrapping various \LaTeX markers around
the linear output from T, in order for it to be in
either math, display math, or numbered equation mode.}
\begin{exports}
math:    & T $\to$ TXT & write in math mode to the stream \asfun{stdout}\\
math:    & (TXT, T) $\to$ TXT & write in math mode to a stream\\
display: & T $\to$ TXT &
write in display math mode to the stream \asfun{stdout}\\
display: & (TXT, T) $\to$ TXT & write in display math mode to a stream \\
equation:& T $\to$ TXT &
write a numbered equation to the stream \asfun{stdout} \\
equation:& (TXT, T) $\to$ TXT & write a numbered equation to a stream \\
\end{exports}
\Aswhere{
TXT &==& TextWriter\\
}
#endif

TeXEquation(T:OutputType): with {
	display: T -> TextWriter;
	display: (TextWriter, T) -> TextWriter;
#if ALDOC
\begin{aspage}{display}
\Usage{ \name~x\\ \name(p, x) }
\Signatures{
\name: & T $\to$ TextWriter\\
\name: & (TextWriter, T) $\to$ TextWriter
}
\Params{
{\em x} & T & The element to write\\
{\em p} & TextWriter & The stream to write to
}
\Descr{
\name(x) writes x to the standard output port \asfun{stdout} in \LaTeX\ display
math mode.\\
\name(p, x) writes x to the output port p in \LaTeX\ display math mode.
}
\Retval{Both functions return the output port after writing to it.}
\begin{asex}
\begin{ttyout}
import from Integer, TeXEquation Integer;
display 130;
\end{ttyout}
writes
\Asoutput{
\> \$\$\\
\> 130\\
\> \$\$
}
to the standard stream \asfun{stdout}.
\end{asex}
\seealso{equation(\this), math(\this)}
\end{aspage}
#endif
	equation: T -> TextWriter;
	equation: (TextWriter, T) -> TextWriter;
#if ALDOC
\begin{aspage}{equation}
\Usage{ \name~x\\ \name(p, x) }
\Signatures{
\name: & T $\to$ TextWriter\\
\name: & (TextWriter, T) $\to$ TextWriter
}
\Params{
{\em x} & T & The element to write\\
{\em p} & TextWriter & The stream to write to
}
\Descr{
\name(x) writes x to the standard output port \asfun{stdout} as a
\LaTeX\ numbered equation.\\
\name(p, x) writes x to the output port p as a \LaTeX\ numbered equation.
}
\Retval{Both routines return the output port after writing to it.}
\begin{asex}
\begin{ttyout}
import from Integer, TeXEquation Integer;
equation 130;
\end{ttyout}
writes
\Asoutput{
\> $\backslash$begin\{equation\}\\
\> 130\\
\> $\backslash$end\{equation\}
}
to the standard stream \asfun{stdout}.
\end{asex}
\seealso{display(\this), math(\this)}
\end{aspage}
#endif
	math: T -> TextWriter;
	math: (TextWriter, T) -> TextWriter;
#if ALDOC
\begin{aspage}{math}
\Usage{ \name~x\\ \name(p, x) }
\Signatures{
\name: & T $\to$ TextWriter\\
\name: & (TextWriter, T) $\to$ TextWriter
}
\Params{
{\em x} & T & The element to write\\
{\em p} & TextWriter & The stream to write to
}
\Descr{
\name(x) writes x to the standard output port \asfun{stdout} in
\LaTeX\ math mode.\\
\name(p, x) writes x to the output port p in \LaTeX\ math mode.
}
\Retval{Both routines return the output port after writing to it.}
\begin{asex}
\begin{ttyout}
import from {Integer, TeXEquation Integer};
math 130;
\end{ttyout}
writes
\Asoutput{ \> \$130\$ }
to the standard stream \asfun{stdout}.
\end{asex}
\seealso{display(\this), equation(\this)}
\end{aspage}
#endif
} == add {
	math(x:T):TextWriter			== math(stdout, x);
	display(x:T):TextWriter			== display(stdout, x);
	equation(x:T):TextWriter		== equation(stdout, x);

	math(p:TextWriter, x:T):TextWriter == {
		import from String;
		p << "$" << x << "$";
	}

	display(p:TextWriter, x:T):TextWriter == {
		import from Character, String;
		p << "$$" << newline << x << newline << "$$" << newline;
	}

	equation(p:TextWriter, x:T):TextWriter == {
		import from Character, String;
		p := p << "\begin{equation}" << newline << x << newline;
		p << "\end{equation}" << newline;
	}
}

