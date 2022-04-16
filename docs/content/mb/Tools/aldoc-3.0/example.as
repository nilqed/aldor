#include "axllib.as"

#if ALDOC

\thistype{Quotient}
\History{L.~Lagaffe}{1/12/94}{created}

\Usage{import from \this~R}

\Params{ \emph{R} & IntegralDomain 
        & an integral domain\\ 
}

\Descr{\this~R forms the quotient field of the 
integral domain \emph{R}}

\begin{exports}
\category{\astype{Field}}\\
\category{\astype{DifferentialExtension} R}\\
$/$: & (R,R) $\to$ \this & take the quotient of two 
ring elements\\
\asexp{coerce}: & R $\to$ \% & coercion from R to \this\\
\asexp{denominator}: & \% $\to$ R & get the denominator of a quotient\\
\asexp{numerator): & \% $\to$ R & get the numerator of a quotient\\
\end{exports}
\begin{exports}[if R has \astype{FiniteCharacteristic} then]
\category{\astype{FiniteCharacteristic}}\\
\end{exports}
\begin{exports}[if R has \astype{GcdDomain} then]
\asexp{normalize}: & \% $\to$ \% & normalize a quotient\\
\end{exports}
#endif

Quotient(R: IntegralDomain):
 Join(Field, DifferentialExtension R) with {
	/:		(R, R) -> %;

#if ALDOC
\aspage{/}

\Usage{n~\name~d}
\Signature{(R,R)}{\%}
\Params{
\emph{n} & R & An element of the ring.\\
\emph{d} & R & An element of the ring.\\
}
\Retval{Returns the quotient \emph{n} over \emph{d}.}
#endif

	if R has FiniteCharacteristic then 
		FiniteCharacteristic;
	coerce:		R -> %;
	
#if ALDOC
\aspage{coerce}

\Usage{\name~x}
\Signature{R}{\%}
\Params{ \emph{x} & R & An element of the ring\\ }
\Retval{Returns the quotient with numerator \emph{x} and 
        denominator 1.
}
#endif

	denominator:	% -> R;
	
#if ALDOC
\aspage{denominator}

\Usage{\name~x}
\Signature{\%}{R}
\Params{ \emph{x} & \% & A quotient\\ }
\Retval{Returns the denominator of a quotient.}
\seealso{\astype{numerator}(\this)}
#endif

	if R has GcdDomain then
		normalize:	% -> %;
		
#if ALDOC
\aspage{normalize}
\Usage{\name~x}
\Signature{\%}{\%}
\Params{ \emph{x} & \% & An quotient\\ }
\Descr{Normalize $x$ by eliminating common divisors of 
       the numerator and denominator.
}
#endif

	numerator:	% -> R;
	
#if ALDOC
\aspage{numerator}                                                  

\Usage{\name~x}
\Signature{\%}{R}
\Params{ \emph{x} & \% & A quotient\\ }
\Retval{Returns the numerator of a quotient.}
\seealso{\astype{denominator}(\this)}
#endif
} == add {....}




