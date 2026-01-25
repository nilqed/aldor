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
----------------------- multlodo.as ------------------------------
--
-- Copyright (c) Manuel Bronstein 2000
-- Copyright (c) INRIA 2000, Version 0.1.13
-- Logiciel Shasta (c) INRIA 2000, dans sa version 0.1.13
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I	== MachineInteger;
	Z	== Integer;
	Q	== Fraction Z;
	Zx	== Fraction ZX;
	Qx	== Fraction QX;
	QFX	== UnivariateFactorialPolynomial(Q, QX);
	QXD	== LinearOrdinaryRecurrence(Q, QX);
	ZXD	== LinearOrdinaryRecurrence(Z, ZX);
	QxY	== DenseUnivariatePolynomial Qx;
	Qxy	== Fraction QxY;
	V	== Vector;
	M	== DenseMatrix;
	UAF	== MonogenicAlgebraOverFraction;
	RATRED	== Record(mode:I, rat: V QxD);
	ALGRED	== Record(mode:I, modulus:QX, c0:Qxy, ratpart:V QxD);
	FACLODO	== Union(rat: RATRED, alg: ALGRED);
	RATSOL	== LinearOrdinaryRecurrenceRationalSolutions;
	SYSSOL	== LinearOrdinaryRecurrenceSystemRationalSolutions;
}

MultiLodo(ZX:UnivariatePolynomialCategory Z,
	QX:UnivariatePolynomialCategory Q,
	QxD:LinearOrdinaryRecurrenceCategory Qx): PartialRing with {
		adjoint: % -> Partial %;
#if ALDOC
\alpage{adjoint}
\Usage{\name~L}
\Params{ {\em L} & $\weyl$ & A difference operator\\ }
\Retval{
Returns $L^\ast E^{m+d}$ where
$$
L^\ast = \sum_{i=d}^m E^{-i} \cdot a_i
$$
is the adjoint of
$$
L = \sum_{i=d}^m a_i E^i
$$
and $\cdot$ is the product in $\weyl$.
}
\Remarks{
Because \name(L) returns $L^\ast E^{m+d}$
rather than the adjoint $L^\ast$,
it follows that \name(\name(L)) returns $E^{-(m+d)} L E^{m+d}$
rather than \emph{L}. 
}
\begin{alex}
It can happen that $L^\ast$ has a nontrivial rational kernel, while
$L$ has a trivial one:
\begin{ttyout}
1 --> L := (n+2)*E^2 + (n^2+3*n+2)*E - n^2 - 3*n - 2;
2 --> tex(kernel(L));
\end{ttyout}
$$
[~]
$$
\begin{ttyout}
3 --> La := adjoint(L);
4 --> tex(La);
\end{ttyout}
$$
\left(-n^{2}-3\,n-2\right)\,E^{2}+\left(n^{2}+n\right)\,E+n
$$
\begin{ttyout}
5 --> tex(kernel(La));
\end{ttyout}
$$
[ {{1} \over {n}} ]
$$
We also verify that $L^{\ast\ast} = E^{-2} L E^{2}$:
\begin{ttyout}
6 --> tex(L * E^(degree(L)) - E^(degree(L)) * adjoint(La));
\end{ttyout}
$$
0
$$
\end{alex}
#endif
		apply: (%, %) -> Partial %;
#if ALDOC
\alpage{apply}
\Usage{\name(L, f)}
\Params{
{\em L} & $\weyl$ & A difference operator\\
{\em f} & $\QQ(n)$ & A rational function\\
}
\Retval{Returns $L(f)$.}
\begin{alex}
We can verify that an element is in the kernel of an operator by applying
the operator to it:
\begin{ttyout}
1 --> L := (n+2)*(n+1)*E^2 -n*(n+1)*E -n;
2 --> K := kernel(L);
3 --> f := element(K, 1);
4 --> tex(f);
\end{ttyout}
$$
-{{1} \over {n}}
$$
\begin{ttyout}
5 --> tex(apply(L, f));
\end{ttyout}
$$
0
$$
\end{alex}
\alseealso{\alexp{shift}}
#endif
		coerce: QX -> %;
		coerce: QxD -> %;
		coerce: M Qx -> %;
		coefficient: (%, %) -> Partial %;
#if ALDOC
\alpage{coefficient}
\Usage{\name(L, m)\\ \name(p, m)}
\Params{
{\em L} & $\weyl$ & A difference operator\\
{\em p} & $\QQ[n]$ & A polynomial\\
{\em m} & $\ZZ$ & An exponent\\
}
\Retval{Returns the coefficient of $E^m$ in $L$ or the
coefficient of $x^m$ in $p$.}
\alseealso{\alexp{degree}}
#endif
		decompose: % -> Partial %;
#if ALDOC
\alpage{decompose}
\Usage{\name~L}
\Params{ {\em L} & $\weyl$ & A difference operator of order at most 3\\ }
\Descr{Returns one of the following possible results:
\begin{itemize}
\item[(i)] \emph{L}, in which case \emph{L} cannot be written as a
least common left multiple of lower order operators
(\emph{L} can still be either reducible or irreducible in that case).
\item[(ii)] $[L_1,\dots,L_m]$ where $L_i \in \weylq$, in which case
\emph{L} is a least common left multiple of $L_1,\dots,L_m$.
\item[(iii)] $[h(n),a(n,E),b(n,E),f_1(n,E),\dots,f_m(n,E)]$,
where $h(n) \in \QQ[n]$ is irreducible and $a(n,E)$,\\
$b(n,E)$,$f_1(n,E),\dots,f_m(n,E) \in \weylq$,
in which case \emph{L} is a least common left multiple of
$f_1(n,E),\dots,f_m(n,E)$ and of $E + a(\alpha, n) / b(\alpha, n)$
where $\alpha$ ranges over all the roots of $h(n)$.
\end{itemize}
}
\begin{alex}
We decompose the difference equation
\begin{equation}
\label{eq:exdecompose}
y(n+3)+(n+2)y(n+2)+(3n^2+9n+6)y(n+1)-(3n^3+9n^2+6n)y(n) = 0
\end{equation}
as follows:
\begin{ttyout}
1 --> L := E^3+(n+2)*E^2+(3*n^2+9*n+6)*E-3*n^3-9*n^2-6*n;
2 --> v := decompose(L);
3 --> tex(v);
\end{ttyout}
$$
\left[ n^{3}-2\,n^{2}+4\,n-6 , \left(-n+1\right)\,E , 1 \right]
$$
This means that the operator of~(\ref{eq:exdecompose}) is a least
common left multiple of $E + (1-\alpha) n$ where $\alpha$
ranges over the roots of $n^{3}-2\,n^{2}+4\,n-6 = 0$.
\end{alex}
\begin{maplerem}
When using \name~from inside \maple, the result returned from
\shasta{} is further transformed into one of the following:
\begin{itemize}
\item[(i)] \emph{L}, in which case \emph{L} cannot be written as a
least common left multiple of lower order operators.
\item[(ii)] An object of the form {\tt LeftLcm}$(L_1,\dots,L_m)$
where the $L_i$'s are difference operators, in which case
\emph{L} is a least common left multiple of $L_1,\dots,L_m$.
\item[(iii)] An object of the form {\tt LeftLcm}$(L_\alpha, and~conjugates)$
where $L_\alpha$ is a difference operator containing an algebraic
number $\alpha$, in which case
\emph{L} is a least common left multiple of all the conjugates of $L_\alpha$.
\end{itemize}
So the above example in \maple{} would be:
\begin{ttyout}
> L := E^3+(n+2)*E^2+(3*n^2+9*n+6)*E-3*n^3-9*n^2-6*n;
> decompose(L, E, n);
\end{ttyout}
$$
{\it LeftLcm}(E+\left (-{\it RootOf}({{\it \_Z}}^{3}-2\,{{\it \_Z}}^{2
}+4\,{\it \_Z}-6)+1\right )n,\mbox {{\tt `and conjugates`}})
$$
\end{maplerem}
\alseealso{\alexp{factor},\alexp{Loewy}}
#endif
		degree: % -> Partial %;
#if ALDOC
\alpage{degree}
\Usage{\name~L\\ \name~p}
\Params{
{\em L} & $\weyl$ & A difference operator\\
{\em p} & $\QQ[n]$ & A polynomial\\
}
\Retval{Returns the degree of $L$ in $E$ or the degree of $p$ in $x$.}
\alseealso{\alexp{coefficient}}
#endif
		dispersion: % -> Partial %;
		dispersion: (%, %) -> Partial %;
#if ALDOC
\alpage{dispersion}
\Usage{\name~p\\ \name(p, q)}
\Params{
{\em p,q} & $\QQ[n]$ & Nonzero polynomials\\
}
\Retval{\name(p,q) returns the largest $m \ge 0$ such that
$\deg(\gcd(p(n),q(n+m)) > 0$,
or $-1$ if that $\gcd(p(n),q(n+m)) = 1$ for all $m \ge 0$,
while \name(p) returns \name(p, p).}
\alseealso{\alexp{spread}}
#endif
		eigenring: % -> Partial %;
#if ALDOC
\alpage{eigenring}
\Usage{\name~L\\ \name~A}
\Params{
{\em L} & $\weyl$ & A difference operator\\
{\em A} & $\QQ(n)^{m,m}$ & A matrix of fractions\\
}
\Descr{
\name(L) returns a basis $R_1,\dots,R_m$ of the eigenring of \emph{L},
\ie the set of operators $R\in \weylq$ of order strictly less than
the order of \emph{L} and such that $L R = S L$ for some operator \emph{S}.\\
\name(A) returns an $m$ by $mt$ matrix $M = [B_1|\dots|B_t]$
such that $B_1,\dots,B_t$ for a basis of the eigenring of $Y(n+1) = A Y$,
\ie~the set of matrices $B\in \QQ(x)^{m,m}$ such that $A B = B(n+1) A$.}
\begin{alex}
We compute the eigenring of the difference equation
\begin{equation}
\label{eq:exeigen}
y(n+2) = 2n(n+1)y(n)
\end{equation}
as follows:
\begin{ttyout}
1 --> L := E^2-2*n*(n+1);
2 --> e := eigenring(L);
3 --> tex(e);
\end{ttyout}
$$
\left[ 1 , {{1} \over {n}}\,E \right]
$$
\end{alex}
\begin{maplerem}
When using \name(A,D,x) from inside \maple, the matrix $[B_1|\dots|B_t]$
returned from \shasta{} is transformed into the array of matrices
$[B_1,\dots,B_t]$.
\end{maplerem}
#endif
		element: (%, %) -> Partial %;
#if ALDOC
\alpage{element}
\Usage{\name(v, k)}
\Params{
{\em v} & $\QQ(n)^m$ & A vector of functions\\
{\em k} & $\ZZ$ & A positive index\\
}
\Retval{Returns the \Th{k} element of $v$, the first element having index $1$.}
#endif
--		extPower: (%, %) -> Partial %; LATER
		exteriorPower: (%, %) -> Partial %;
#if ALDOC
\alpage{exteriorPower}
\Usage{\name(L, m)}
\Params{
{\em L} & $\weyl$ & A difference operator\\
{\em m} & $\ZZ$ & A positive integer\\
}
\Retval{
Returns a difference operator $\extpow{L}{n}$
of minimal order whose kernel is generated by the Casoratians of $n$ elements
of a basis of $\Ker(L)$.
}
\begin{alex}
The second exterior power of
$$
L = E^4-E-n
$$
can be computed as follows:
\begin{ttyout}
1 --> L :=  E^4-E-n;
2 --> Le2 := exteriorPower(L,2);
3 --> tex(Le2);
\end{ttyout}
$$
E^{6}+\left(n+2\right)\,E^{4}-E^{3}-\left(n^{2}+5\,n+6\right)\,
E^{2}-n^{3}-3\,n^{2}-2\,n
$$
To prove that $L$ is irreducible, it is sufficient to check that neither
$L$, its adjoint or its second exterior power has a hypergeometric solution
over $\QQ$, and that the eigenring of $L$ is trivial:
\begin{ttyout}
4 --> tex(hyper(L));
\end{ttyout}
$$
[~]
$$
\begin{ttyout}
5 --> tex(hyper(adjoint(L)));
\end{ttyout}
$$
[~]
$$
\begin{ttyout}
6 --> tex(hyper(Le2));
\end{ttyout}
$$
[~]
$$
\begin{ttyout}
7 --> tex(eigenring(L));
\end{ttyout}
$$
[ 1 ]
$$
\end{alex}
#endif
		factor: % -> Partial %;
#if ALDOC
\alpage{factor}
\altarget{efactor}
\Usage{\name~L}
\Params{ {\em L} & $\weyl$ & A difference operator of order at most 3\\ }
\Descr{Returns one of the following possible results:
\begin{itemize}
\item[(i)] \emph{L}, in which case \emph{L} is irreducible
in ${\overline \QQ}(n)[E]$.
\item[(ii)] $[m,L_1,\dots,L_t]$ where $m \ge 0$ and $L_i \in \weylq$,
in which case each $L_t$ is irreducible in ${\overline \QQ}(n)[E]$,
and L can be expressed in terms of the $L_i$'s depending on $m$
as in the following table:
\begin{center}
\begin{tabular}{c|l}
\emph{m} & \emph{L}\\
\hline
0 & LeftLcm($L_1,\dots,L_t$)\\
1 & $L_1 \cdots L_t$\\
2 & LeftLcm($L_1, L_2 L_3$)\\
3 & $L_1$ LeftLcm($L_2, L_3$)\\
4 & $L_1$ LeftLcm($L_2, L_3$) $L_4$\\
\end{tabular}
\end{center}
\item[(iii)] $[m,h(n),a(n,E),b(n,E),f_1(n,E),\dots,f_t(n,E)]$,
where $m < 0$, $h(n) \in \QQ[n]$ is irreducible and $a(n,E)$,
$b(n,E)$, $f_1(n,E),\dots,f_t(n,E) \in \weylq$,
in which case each $f_i(n,E)$ is irreducible in ${\overline \QQ}(n)[E]$,
and \emph{L} can be expressed depending on $m$ as in the following table:
\begin{center}
\begin{tabular}{c|l}
\emph{m} & \emph{L}\\
\hline
-1 & LeftLcm($E + a(\alpha, n)/b(\alpha, n), f_1(n,E),\dots,f_t(n,E)$)\\
-4 & $f_1(n,E)$ LeftLcm($E + a(\alpha, n)/b(\alpha, n)$)\\
-5 & $f_1(n,E)$ LeftLcm($E + a(\alpha, n)/b(\alpha, n)$) $f_2(n,E)$\\
\end{tabular}
\end{center}
\item[(iii)] $[m,h(n),a(n,E),b(n,E),f_1(n,E),\dots,f_t(n,E)]$,
where $m < 0$, $h(n) \in \QQ[n]$ is irreducible and $a(n,E)$,
$b(n,E)$, $f_1(n,E),\dots,f_t(n,E) \in \QQ(n)[E]$,
in which case each $f_i(n,D)$ is irreducible in ${\overline \QQ}(n)[E]$,
and \emph{L} can be expressed depending on $m$ as in the following table:
\begin{center}
\begin{tabular}{c|l}
\emph{m} & \emph{L}\\
\hline
-1 & LeftLcm($E + a(\alpha, n)/b(\alpha, n), f_1(n,E),\dots,f_t(n,E)$)\\
-4 & $f_1(n,E)$ LeftLcm($E + a(\alpha, n)/b(\alpha, n)$)\\
-5 & $f_1(n,E)$ LeftLcm($E + a(\alpha, n)/b(\alpha, n)$) $f_2(n,E)$\\
\end{tabular}
\end{center}
where $\alpha$ ranges over all the roots of $h(n)$.
\end{itemize}
}
\begin{alex}
We factor the difference equation
\begin{equation}
\label{eq:exfactor}
y(n+3) - (n+2)y(n+2) + (3n^2+3n)y(n+1) - (3n^3+3n^2)y(n) = 0
\end{equation}
as follows:
\begin{ttyout}
1 --> L := E^3+(-n-2)*E^2+(3*n^2+3*n)*E-3*n^3-3*n^2;
2 --> v := factor(L);
3 --> tex(v);
\end{ttyout}
$$
\left[ -5 , n^{2}+3 , -\left(n\,E\right) , 1 , 1 , E-n \right]
$$
This means that the operator of~(\ref{eq:exfactor}) can be written
in the form
$$
L = \mbox{LCLM}(E - \sqrt{-3} n, E + \sqrt{-3} n) (E - n)
$$
\end{alex}
\begin{maplerem}
In order not to conflict with the {\tt factor}
function in \maple, \name~is available under \maple{} under the name
{\tt efactor}.
In addition, when using {\tt efactor} from inside \maple,
the result returned from
\shasta{} is further transformed as in the case of
the \alexp{decompose} function.
So the above example in \maple{} would be:
\begin{ttyout}
> L := E^3+(-n-2)*E^2+(3*n^2+3*n)*E-3*n^3-3*n^2;
> efactor(L, E, n);
\end{ttyout}
$$
\left[1,{\it LeftLcm}(E+-i\sqrt {3}n,E+i\sqrt {3}n),E-n\right]
$$
\end{maplerem}
\alseealso{\alexp{decompose},\alexp{Loewy}}
#endif
		hyper: % -> Partial %;
#if ALDOC
\alpage{hyper}
\Usage{\name~L}
\Params{ {\em L} & $\weyl$ & A difference operator\\ }
\Retval{Returns $[]$ if $L y = 0$ has no hypergeometric solution over $\QQ(n)$,
or $f(n)$ such that any solution of $y(n+1) = f(n) y(n)$
is also a solution of $L y = 0$.}
\Remarks{\name~returns only the solutions that are hypergeometric
over $\QQ(n)$, \ie~the solutions $y$ such that $y(n+1)/y(n) \in \QQ(n)$.
It does not return any eventual solution that is hypergeometric over
$\overline{\QQ}(n)$ but not over $\QQ(n)$.
In addition, \name~does not attempt to return several linearly
independent hypergeometric solutions, so if it finds one, there could
be some others.}
\begin{alex}
The equation
$$
L = (n-1)y(n+2) - (n^2+3n-2)y(n+1) + 2n(n+1)y(n) = 0
$$
has hypergeometric solutions:
\begin{ttyout}
1 --> L := (n-1)*E^2 - (n^2+3*n-2)*E + 2*n*(n+1);
2 --> tex(hyper(L));
\end{ttyout}
$$
2
$$
This shows that $2^n$ is a solution, but there are others: we can
verify that $E - n - 1$ divides $L$ on the right, which proves
that $n!$ is another hypergeometric solution:
\begin{ttyout}
3 --> R := E - n - 1; 
4 --> Q := L / R;
5 --> tex(L - Q*R);
\end{ttyout}
$$
0
$$
\end{alex}
#endif
		kernel: % -> Partial %;
		-- second argument = denoms, last argument = degree bound
--		kernel: (%, List %, %) -> Partial %; LATER
#if ALDOC
\alpage{kernel}
\altarget{polynomialKernel}
\altarget{rationalKernel}
% \Usage{\name~L \\ \name(L, p) \\ \name~A \\ \name(A, p)}
\Usage{\name~L \\ \name~A}
\Params{
{\em L} & $\weyl$ & A difference operator\\
{\em A} & $\QQ(n)^{m,m}$ & A matrix of fractions\\
% {\em p} & $\QQ[n]$ & A polynomial\\
}
\Descr{\name~L returns a basis for $\Ker~L \cap \QQ(n)$, while
\name~A returns a basis for $\Ker(Y(n+1) = A Y(n)) \cap \QQ(x)^m$.
% In both cases, if a second argument $p$ is present, then a basis for the
% subspace of all solutions whose denominator $b \in \QQ[n]$
% has all its roots among the roots of $p$.
% For example, \name(L, 1) returns a basis for $\Ker~L \cap \QQ[n]$,
% the space of all the polynomial solutions of $L y = 0$.
}
\begin{alex}
The equation
$$
L = (n+2)(n+4)y(n+2)-(2(n+1)(n+3)+1)y(n+1)+(n+1)^2 y(n) = 0
$$
has the following rational solutions:
\begin{ttyout}
1 --> L := (n+2)*(n+4)*E^2-(2*(n+1)*(n+3)+1)*E+(n+1)^2;
2 --> K := kernel(L);
3 --> tex(K);
\end{ttyout}
$$
[{{1} \over {n^{2}+3\,n+2}}]
$$
\end{alex}
\begin{maplerem}
In order not to conflict with the {\tt linalg[kernel]}
function in \maple, \name~is available under \maple under the names
\alexp{polynomialKernel} and \alexp{rationalKernel}.
So the above examples in \maple would be:
\begin{ttyout}
> L := (n+2)*(n+4)*E^2-(2*(n+1)*(n+3)+1)*E+(n+1)^2;
> rationalKernel(L,E,n);
\end{ttyout}
$$
\left[{{1} \over {n^{2}+3\,n+2}}\right]
$$
\end{maplerem}
\alseealso{%\alexp{parametricKernel},
\alexp{polynomialSolution}, \alexp{rationalSolution}}
#endif
		leftGcd: (%, %) -> Partial %;
#if ALDOC
\alpage{leftGcd}
\Usage{\name(A, B)\\ \name(p, q)}
\Params{
{\em A, B} & $\weyl$ & Difference operators\\
{\em p, q} & $\QQ[n]$ & Polynomials\\
}
\Retval{
\name(A, B) returns $G$ such that $A = G S$, $B = G T$, and every other
exact left divisor of $A$ and $B$ is a left divisor of $G$, while
\name(p, q) returns $\gcd(p, q)$.
}
\alseealso{\alexp{leftLcm}, \alexp{rightGcd}, \alexp{rightLcm}}
#endif
		leftLcm: (%, %) -> Partial %;
#if ALDOC
\alpage{leftLcm}
\Usage{\name(A, B)\\ \name(p, q)}
\Params{
{\em A, B} & $\weyl$ & Difference operators\\
{\em p, q} & $\QQ[n]$ & Polynomials\\
}
\Retval{
\name(A, B) returns $L$ such that $L = S A = T B$, and every other
left multiple of $A$ and $B$ is a left multiple of $L$, while
\name(p, q) returns $\lcm(p, q)$.
}
\begin{alex}
An annihilator of $2^n + n!$ can be obtained by computing the
least common left multiple of the annihilators $L_1 = E - 2$ and
$L_2 = E - n - 1$ of $2^n$ and $n!$ respectively:
\begin{ttyout}
1 --> L1 := E-2;
2 --> L2 := E-n-1;
3 --> L := leftLcm(L1, L2);
4 --> tex(L);
\end{ttyout}
$$
E^{2}+{{-n^{2}-3\,n+2} \over {n-1}}\,E+{{2\,n^{2}+2\,n} \over {n-1}}
$$
\end{alex}
\alseealso{\alexp{leftGcd}, \alexp{rightGcd}, \alexp{rightLcm}}
#endif
		liouvillianSolution: % -> Partial %;
#if LATER_ALDOC
\alpage{liouvillianSolution}
\Usage{\name~L}
\Params{ {\em L} & $\weyl$ & A difference operator\\ }
\Retval{Returns $[]$ if $L y = 0$ has no Liouvillian solution over $\QQ$.
Otherwise, it returns $[f_1(n),\dots,f_m(n)]$
such that the interlacing of $y_1,\dots,y_m$ is a solution of $L y = 0$
where each $y_i$ is a solution of $y_i(n+1) = f_i(n) y_i(n)$.}
\Remarks{Note that \name~does not attempt to return several linearly
independent Liouvillian solutions, so if it finds one, there could
be some others. In addition, a return value of $[]$ proves that there
are no Liouvillian solutions over $\QQ$, but there could be Liouvillian
solutions over its algebraic closure.}
\begin{alex}
The equation
\begin{eqnarray*}
L := (n+2)(n^5+2n^4+n^3-1)y(n+2) &+& (n+1)(5n^2+8n+4)y(n+1)\\
       &-& n^2 (n^5+7n^4+19n^3+25n^2+16n+3) y(n) = 0
\end{eqnarray*}
s no hypergeometric solutions, but it does have Liouvillian solutions:
\begin{ttyout}
1 --> L := (n+2)*(n^5+2*n^4+n^3-1)*E^2 + (n+1)*(5*n^2+8*n+4)*E
          - n^2 * (n^5+7*n^4+19*n^3+25*n^2+16*n+3);
2 --> tex(hyper(L));
\end{ttyout}
$$
[~]
$$
\begin{ttyout}
3 --> tex(liouvillianSolution(L));
\end{ttyout}
$$
[{{2\,n^{2}+3\,n+1} \over {n}}, {{2\,n^{2}+5\,n+3} \over {n+{{1} \over {2}}}}]
$$
This means that $Ly=0$ has for solution the interlacing of the hypergeometric
sequences $z_1$ and $z_2$ defined by
$$
z_1(n+1) = {{2\,n^{2}+3\,n+1} \over {n}} z_1(n)
$$
and
$$
z_2(n+1) = {{2\,n^{2}+5\,n+3} \over {n+{{1} \over {2}}}} z_2(n)
$$
\end{alex}
#endif
		-- list: List % -> Partial %;
		Loewy: % -> Partial %;
#if ALDOC
\alpage{Loewy}
\Usage{\name~L}
\Params{ {\em L} & $\weyl$ & A difference operator of order at most 3\\ }
\Retval{Returns either \emph{L}, in which case \emph{L} is completely
reducible, or a right Loewy decomposition $[L_1,\dots,L_t]$
where $L = L_1 \cdots L_t$ and each $L_i \in \weylq$ is a completely reducible
right-factor of maximal order of $L_1 \cdots L_{i-1}$.
}
\begin{alex}
We compute the Loewy decomposition of the difference equation
\begin{equation}
\label{eq:exloewy}
y(n+3) - n y(n+2) + (3n^2+9n+6)y(n+1) -(3n^3+3n^2)y(n) = 0
\end{equation}
as follows:
\begin{ttyout}
1 --> L := E^3-n*E^2+(3*n^2+9*n+6)*E-3*n^3-3*n^2;
2 --> v := Loewy(L);
3 --> tex(v);
\end{ttyout}
$$
\left[ E-n , E^{2}+3\,n^{2}+3\,n \right]
$$
This means that the operator of~(\ref{eq:exloewy}) factors as
$$
\paren{E-n}\paren{E^{2}+3\,n^{2}+3\,n}
$$
where the second-order factor is a completely reducible right-factor
of maximal order. Note that is is reducible in this example:
\begin{ttyout}
4 --> w := decompose(element(v,2));
5 --> tex(w);
\end{ttyout}
$$
\left[ n^{2}+3 , -\left(n\,E\right) , 1 \right]
$$
which means that
$E^{2}+3\,n^{2}+3\,n$
is a least common left multiple of $E - n \sqrt{-3}$ and $E + n \sqrt{-3}$.
\end{alex}
\alseealso{\alexp{decompose},\alexp{factor}}
#endif
		makeIntegral: % -> Partial %;
#if ALDOC
\alpage{makeIntegral}
\Usage{\name~L}
\Params{ {\em L} & $\weyl$ & A difference operator\\ }
\Retval{Returns the primitive multiple of $L$ in $\weyl$.}
\begin{alex}
\begin{ttyout}
1 --> L := E^2 - E/n + n+1;
2 --> tex(makeIntegral(L));
\end{ttyout}
$$
n\,E^{2}-E+n^{2}+n
$$
\end{alex}
\alseealso{\alexp{normalize}}
#endif
		normalize: % -> Partial %;
#if ALDOC
\alpage{normalize}
\Usage{\name~L \\ \name~p}
\Params{
{\em L} & $\weyl$ & A difference operator\\
{\em p} & $\QQ[n]$ & A polynomial\\
}
\Descr{\name~makes its argument monic in the outermost variable.}
\Remarks{\name~can also be used on vectors and quotients of polynomials.}
\begin{alex}
\begin{ttyout}
1 --> L := n*E^2 - E + n^2 + n;
2 --> tex(normalize(L));
\end{ttyout}
$$
E^{2}-{{1} \over {n}}\,E+n+1
$$
\begin{ttyout}
3 --> f := (2*n + 1)/(3*n^2 - 1);
4 --> tex(normalize(f));
\end{ttyout}
$$
{{n+{{1} \over {2}}} \over {n^{2}-{{1} \over {3}}}}
$$
\end{alex}
\alseealso{\alexp{makeIntegral}}
#endif
--		parametricKernel: (%, List %) -> Partial %;
#if LATER_ALDOC
\alpage{parametricKernel}
\Usage{\name(L, $g_1,\dots,g_m$)}
\Params{
{\em L} & $\weyl$ & A difference operator\\
{\em $g_i$} & $\QQ(x)$ & Fractions\\
}
\Descr{\name(L,$g_1,\dots,g_m$) returns a
matrix $M$ with $r + m$ columns and of the form
\begin{equation}
\label{eq:paramkernel}
M = \left[\begin{array}{c} A\cr h_1 \dots h_r 0 \dots 0\end{array}\right]
\end{equation}
where $h_1,\dots,h_r \in \QQ(x)$ and $A$ has coefficients in $\QQ$.
Any solution $y \in \QQ(x)$, $c_1,\dots,c_m \in \QQ$ of
$L y = \sum_{i=1}^m c_i g_i$ must be of the form
$$
y = \sum_{j=1}^r d_j h_j
\quad\mbox{ where }\quad
d_1,\dots,d_r \in \QQ
\mbox{ and }
A (d_1,\dots,d_r,c_1,\dots,c_m)^T = 0\,.
$$
}
\begin{alex}
The rational solutions of
$$
(x^{4}+x^{2})\frac{d^2y}{dx^2}+(3x^{5}+5x^{3}+4x)\frac{dy}{dx}
+(2x^{6}+6x^{4}+6x^{2}+2) y = c (2x^{7}+9x^{5}+11x^{3}+6x)
$$
can be computed in the following way:
\begin{ttyout}
1 --> L := (x^4+x^2)*D^2+(3*x^5+5*x^3+4*x)*D+2*x^6+6*x^4+6*x^2+2;
2 --> K := parametricKernel(L,2*x^7+9*x^5+11*x^3+6*x);
3 --> tex(K);
\end{ttyout}
$$
\pmatrix{
6 & -6 \cr 
11 & -11 \cr 
9 & -9 \cr 
2 & -2 \cr 
x & 0\cr } 
$$
So any rational solution of $L y = c (2x^{7}+9x^{5}+11x^{3}+6x)$
must be of the form $y = d x$ where
$$
\pmatrix{
6 & -6 \cr
11 & -11 \cr
9 & -9 \cr
2 & -2 \cr
} \pmatrix{ d \cr c } = \pmatrix{ 0 \cr 0 }
$$
\ie any solution is of the form $y = c x$ for an arbitrary constant $c$.
\end{alex}
\begin{maplerem}
When using \name~from inside \maple, the output is modified and
the structure
$$
[[h_1,\dots,h_r], A]
$$
is returned, where $A$ and the $h_i$'s are as in~(\ref{eq:paramkernel}).
So the above example in \maple would be:
\begin{ttyout}
> L := (x^4+x^2)*D^2+(3*x^5+5*x^3+4*x)*D+2*x^6+6*x^4+6*x^2+2;
> parametricKernel(L,2*x^7+9*x^5+11*x^3+6*x,D,x);
\end{ttyout}
$$
\left[ [n],
\left[\matrix{
6 & -6 \cr 
11 & -11 \cr 
9 & -9 \cr 
2 & -2 \cr 
}
\right]\right]
$$
\end{maplerem}
\alseealso{\alexp{kernel}, \alexp{polynomialSolution}, \alexp{rationalSolution}}
#endif
		polynomialSolution: (%, %) -> Partial %;
#if ALDOC
\alpage{polynomialSolution}
\Usage{\name(L, g)}
\Params{
{\em L} & $\weyl$ & A difference operator\\
{\em g} & $\QQ[n]$ & A polynomial\\
}
\Descr{\name($L,g$) returns either $[p]$ where $p \in \QQ[n]$
satisfies $L p = g$, or $[]$ if $L y = g$ has no solution in $\QQ[n]$.}
\Remarks{\name($L,0$) returns $[0]$ only when $L y = 0$ has no nonzero
polynomial solution.}
\begin{alex}
A particular polynomial solution of
$$
y(n+1) - y(n) = 5 n^4
$$
can be computed in the following way:
\begin{ttyout}
1 --> p := polynomialSolution(E-1,5*n^4);
2 --> tex(p);
\end{ttyout}
$$
[ n^{5}-{{5} \over {2}}\,n^{4}+{{5} \over {3}}\,n^{3}-{{1} \over {6}}\,n ]
$$
\end{alex}
\begin{maplerem}
When using \name~from inside \maple, the output is modified and
either a polynomial solution in $p \in \QQ[n]$ or $[]$ is returned.
So the above example in \maple would be:
\begin{ttyout}
> polynomialSolution(E-1,5*n^4,E,n);
\end{ttyout}
$$
n^{5}-{{5} \over {2}}\,n^{4}+{{5} \over {3}}\,n^{3}-{{1} \over {6}}\,n
$$
\end{maplerem}
\alseealso{\alexp{kernel},
% \alexp{parametricKernel},
\alexp{rationalSolution}}
#endif
		rationalSolution: (%, %) -> Partial %;
#if ALDOC
\alpage{rationalSolution}
\Usage{\name(L, g)}
\Params{
{\em L} & $\weyl$ & A difference operator\\
{\em g} & $\QQ(n)$ & A fraction\\
}
\Descr{\name($L,g$) returns either $[f]$ where $f \in \QQ(x)$
satisfies $L f = g$, or $[]$ if $L y = g$ has no solution in $\QQ(x)$.}
\Remarks{\name($L,0$) returns $[0]$ only when $L y = 0$ has no nonzero
rational solution.}
\begin{maplerem}
When using \name~from inside \maple, the output is modified and
either a rational solution in $f \in \QQ(n)$ or $[]$ is returned.
\end{maplerem}
\alseealso{\alexp{kernel},
% \alexp{parametricKernel},
\alexp{polynomialSolution}}
#endif
		rightGcd: (%, %) -> Partial %;
#if ALDOC
\alpage{rightGcd}
\Usage{\name(A, B)\\ \name(p, q)}
\Params{
{\em A, B} & $\weyl$ & Difference operators\\
{\em p, q} & $\QQ[n]$ & Polynomials\\
}
\Retval{
\name(A, B) returns $G$ such that $A = S G$, $B = T G$, and every other
exact right divisor of $A$ and $B$ is a right divisor of $G$, while
\name(p, q) returns $\gcd(p, q)$.
}
\begin{alex}
To look for closed-form common solutions of the difference equations
\begin{equation}
y(n+3)-\left(n+4\right)\,y(n+2)+2\,y(n+1)+(n^{2}+n) y(n) = 0
\label{eq:exrgcd1}
\end{equation}
and
\begin{equation}
y(n+2)-\left(n+4\right)\,y(n+1)+(2\,n+2)y(n) = 0
\label{eq:exrgcd2}
\end{equation}
we look for solutions of their greatest right common divisor as follows:
\begin{ttyout}
1 --> L1 := E^3-(n+4)*E^2+2*E+n^2+n;
2 --> L2 := E^2-(n+4)*E+2*n+2;
3 --> L := rightGcd(L1, L2);
4 --> tex(L);
\end{ttyout}
$$
E-n-1;
$$
This means that the solutions of
the system~(\ref{eq:exrgcd1})-(\ref{eq:exrgcd2}) are of the
form $y = c n!$ for any constant $c$.
\end{alex}
\alseealso{\alexp{leftGcd}, \alexp{leftLcm}, \alexp{rightLcm}}
#endif
		rightLcm: (%, %) -> Partial %;
#if ALDOC
\alpage{rightLcm}
\Usage{\name(A, B)\\ \name(p, q)}
\Params{
{\em A, B} & $\weyl$ & Difference operators\\
{\em p, q} & $\QQ[n]$ & Polynomials\\
}
\Retval{
\name(A, B) returns $L$ such that $L = A S = B T$, and every other
right multiple of $A$ and $B$ is a right multiple of $L$, while
\name(p, q) returns $\lcm(p, q)$.
}
\alseealso{\alexp{leftGcd}, \alexp{leftLcm}, \alexp{rightGcd}}
#endif
--		section: (%, %) -> Partial %;
		sections: (%, %) -> Partial %;
#if ALDOC
\alpage{sections}
\Usage{\name(f, m)}
\Params{
{\em L} & $\weyl$ & A difference operator\\
{\em m} & $\ZZ$ & A positive integer\\
}
\Retval{Returns $[L_0,\dots,L_{m-1}]$ of minimal orders
such that for any solution $y = (y_0,y_1,y_2,\dots)$ of $L y = 0$,
the sequences $y^{(i)} = (y_i, y_{i+m}, y_{i+2m},\dots)$ for $0 \le i < m$
satisfy $L_i y^{(i)} = 0$.}
\begin{alex}
The $2$-sections of
\begin{eqnarray*}
L := (n+2)(n^5+2n^4+n^3-1)y(n+2) &+& (n+1)(5n^2+8n+4)y(n+1)\\
        &-& n^2 (n^5+7n^4+19n^3+25n^2+16n+3) y(n) = 0
\end{eqnarray*}
are computed as follows:
\begin{ttyout}
1 --> L := (n+2)*(n^5+2*n^4+n^3-1)*E^2 + (n+1)*(5*n^2+8*n+4)*E
           - n^2 * (n^5+7*n^4+19*n^3+25*n^2+16*n+3);
2 --> L2 := sections(L,2);
3 --> tex(L2);
\end{ttyout}
\begin{eqnarray*}
[
\left(40\,n^{3}+112\,n^{2}+72\,n+16\right)\,E^{2}&-&
\left(160\,n^{4}+568\,n^{3}+760\,n^{2}+448\,n+96\right)\,E \\
&+&160\,n^{5}+528\,n^{4}+544\,n^{3}+160\,n^{2},\\
\left(40\,n^{3}+172\,n^{2}+214\,n+85\right)\,E^{2}&-&
\left(160\,n^{4}+888\,n^{3}+1852\,n^{2}+1714\,n+591\right)\,E\\
&+& 160\,n^{5}+928\,n^{4}+2000\,n^{3}+1968\,n^{2}+882\,n+146
]
\end{eqnarray*}
Those turn out to have hypergeometric solutions, which yields a Liouvillian
solution of $Ly = 0$:
\begin{ttyout}
4 --> tex(hyper(element(L2,1)));
\end{ttyout}
$$
{{2\,n^{2}+3\,n+1} \over {n}}
$$
\begin{ttyout}
5 --> tex(hyper(element(L2,2)));
\end{ttyout}
$$
{{2\,n^{2}+5\,n+3} \over {n+{{1} \over {2}}}}
$$
\end{alex}
#endif
		shift: (%, %) -> Partial %;
#if ALDOC
\alpage{shift}
\Usage{\name~f\\\name(f, m)}
\Params{
{\em f} & $\QQ(n)$ & The function to shift\\
{\em m} & $\ZZ$ & The shift order (optional)\\
}
\Retval{
\name~f returns $f(n+1)$, the shift of $f$.\\
\name(f, m) returns $f(n+m)$, the \Th{m} shift of $f$.
}
\alseealso{\alexp{apply}}
#endif
		spread: % -> Partial %;
		spread: (%, %) -> Partial %;
#if ALDOC
\alpage{spread}
\Usage{\name~p\\ \name(p, q)}
\Params{
{\em p,q} & $\QQ[n]$ & Nonzero polynomials\\
}
\Retval{\name(p,q) returns
$\{ m \ge 0 \st \deg(\gcd(p(n),q(n+m)) > 0\}$,
while \name(p) returns \name(p, p).}
\alseealso{\alexp{dispersion}}
#endif
		system: % -> Partial %;
		system: (I, List %) -> Partial %;
#if ALDOC
\alpage{system}
\Usage{\name($a_{11},a_{12},\dots,a_{nn}$)\\ \name(L)}
\Params{
{\em $a_{ij}$} & $\QQ(x)$ & The entries of a square matrix\\
{\em L} & $\weyl$ & A difference operator\\
}
\Retval{\name($a_{11},\dots,a_{nn}$) returns the
system $Y(n+1) = A Y(n)$, where $A$ is the square matrix
given by the $a_{ij}$'s, while \name(L) returns the
companion system associated with the operator L.}
\Remarks{The entries of the matrix must be listed by rows.}
\begin{alex}
The system
$$
\left(\begin{array}{c} y_1(n+1) \\ y_2(n+1) \end{array}\right) =
\left(\begin{array}{cc}
{{2\,n+4} \over {n+1}} & {{-n-2} \over {n}} \cr 
1 & 0\cr
\end{array}\right)
\left(\begin{array}{c} y_1(n) \\ y_2(n) \end{array}\right)
$$
has the following rational kernel:
\begin{ttyout}
1 --> A := system((2*n^2+4*n)/(n^2+n),(-n^2-3*n-2)/(n^2+n),1,0);
2 --> K := kernel(A);
3 --> tex(K);
\end{ttyout}
$$
\pmatrix{
{{1} \over {2}}\,n^{2}+{{1} \over {2}}\,n &
-{{1} \over {2}}\,n^{2}+{{1} \over {2}}\,n+1 \cr 
{{1} \over {2}}\,n^{2}-{{1} \over {2}}\,n &
-{{1} \over {2}}\,n^{2}+{{3} \over {2}}\,n\cr }
$$
\end{alex}
#endif
} == add {
	Rep == Union(Lodo:QxD, Vec:V QxD, Mat:M Qx);
	import from Rep;

	0:%			== per [0@QxD];
	1:%			== per [1@QxD];
	coerce(n:Z):%		== n::QxD::%;
	coerce(p:QX):%		== { import from Qx; p::Qx::QxD::%; }
	coerce(l:QxD):%		== per [l];
	coerce(A:M Qx):%	== per [A];
	local vec?(a:%):Boolean	== rep(a) case Vec;
	local mat?(a:%):Boolean	== rep(a) case Mat;
	local lodo?(a:%):Boolean== rep(a) case Lodo;
	local lodo(a:%):QxD	== rep(a).Lodo;
	local mat(a:%):M Qx	== rep(a).Mat;
	local vec(a:%):V(QxD)	== rep(a).Vec;
	- (a:%):Partial %	== { lodo? a => [(- lodo a)::%]; failed; }
	leftLcm(a:%, b:%):Partial %	== lodolcm(a, b, leftLcm);
	rightLcm(a:%, b:%):Partial %	== lodolcm(a, b, rightLcm);
	rightGcd(a:%, b:%):Partial %	== lodogcd(a, b, rightGcd);
	leftGcd(a:%, b:%):Partial %	== lodogcd(a, b, leftGcd);
	section(a:%, b:%):Partial %	== lodopos(a, b,sparseLeftMultiple$QxD);
	sections(a:%, b:%):Partial %	== lodonpos(a,b,1$Z,lodoSections);
	dispersion(a:%, b:%):Partial %	== polynz(a, b, disp);
	dispersion(a:%):Partial %	== polynz(a, disp);
	spread(a:%, b:%):Partial %	== polynz(a, b, sprd);
	spread(a:%):Partial %		== polynz(a, sprd);
	local disp(a:ZX, b:ZX):%	== dispersion(a, b)::%;
	local disp(a:ZX):%		== dispersion(a)::%;
	local ident(f:Qx):Qx		== f;

	exteriorPower(a:%, b:%):Partial %	== lodopos(a, b, extpow);

	Loewy(a:%):Partial % == {
		import from I, Z, Q, QX, Qx, V QxD, UAF(QX, QXD, Qx, QxD);
		(~lodo? a) or ((d := degree(L := lodo a)) > 3) => failed;
		d < 2 => [a];
		(c1, L1) := makeIntegral L;	-- L1 = c1 L,  L = 1/c1 L1
		(c2, L2) := makez0 L1;		-- L2 = c2 L1, L = 1/(c1 c2) L2
		v := { d = 2 => Loewy2 L2; Loewy3 L2 }
		one?(#v) => [a];
		v.1 := inv((c2 * c1)::Qx) * v.1;
		[per [v]];
	}

	local Loewy2(L:ZXD):V QxD == {
		import from Q;
		import from SecondOrderLinearOrdinaryRecurrenceSolver(Z, Q,
						coerce, ZX, ZXD, QX, QxD, QxY);
		Loewy L;
	}

	local Loewy3(L:ZXD):V QxD == {
		import from Q;
		import from ThirdOrderLinearOrdinaryRecurrenceSolver(Z, Q,
						coerce, ZX, ZXD, QX, QxD, QxY);
		Loewy L;
	}

	decompose(a:%):Partial % == {
		import from Z;
		(~lodo? a) or ((d := degree(L := lodo a)) > 3) => failed;
		d < 2 => [a];
		L2 := makez makepoly(QXD, QxD, L);
		d = 2 => [decompose2(a, L2)];
		[decompose3(a, L2)];
	}

	local decompose2(a:%, L:ZXD):% == {
		import from Q;
		import from SecondOrderLinearOrdinaryRecurrenceSolver(Z, Q,
						coerce, ZX, ZXD, QX, QxD, QxY);
		decompose0(a, decompose L);
	}

	local decompose3(a:%, L:ZXD):% == {
		import from Q;
		import from ThirdOrderLinearOrdinaryRecurrenceSolver(Z, Q,
						coerce, ZX, ZXD, QX, QxD, QxY);
		decompose0(a, decompose L);
	}

	local decompose0(a:%, u:FACLODO):% == {
		import from I, V QxD, Qx, QxY, Qxy, V QxY, RATRED, ALGRED;
		u case rat => {
			assert(zero?(u.rat.mode));	-- LCLM
			one?(#(v := u.rat.rat)) => a;	-- indecomposable
			per [v];
		}
		assert(zero?(u.alg.mode));		-- LCLM
#if LATER_WHEN_V(QxY)_IS_IN_REP
		h := u.alg.modulus::Qx::QxY;
		unum := numerator(u.alg.c0);
		uden := denominator(u.alg.c0);
#else
		h := u.alg.modulus::Qx::QxD;
		unum := QxY2QxD numerator(u.alg.c0);
		uden := QxY2QxD denominator(u.alg.c0);
#endif
		zero? #(v := u.alg.ratpart) => per [[h, unum, uden]];
		assert(one? #v);
#if LATER_WHEN_V(QxY)_IS_IN_REP
		per [[h, unum, uden, QxD2QxY(v.1)]];
#else
		per [[h, unum, uden, v.1]];
#endif
	}

	local QxY2QxD(L:QxY):QxD == {
		import from MonogenicAlgebra2(Qx, QxY, Qx, QxD);
		map(ident)(L);
	}

	local QxD2QxY(L:QxD):QxY == {
		import from MonogenicAlgebra2(Qx, QxD, Qx, QxY);
		map(ident)(L);
	}

	factor(a:%):Partial % == {
		import from Z, Qx, V QxD, UAF(QX, QXD, Qx, QxD);
		(~lodo? a) or ((d := degree(L := lodo a)) > 3) => failed;
		d < 2 => [a];
		(c1, L1) := makeIntegral L;	-- L1 = c1 L,  L = 1/c1 L1
		(c2, L2) := makez0 L1;		-- L2 = c2 L1, L = 1/(c1 c2) L2
		d = 2 => [factor2(a, L2, c1, c2)];
		[factor3(a, L2, c1, c2)];
	}

	local factor2(a:%, L:ZXD, c1:QX, c2:Z):% == {
		import from Q;
		import from SecondOrderLinearOrdinaryRecurrenceSolver(Z, Q,
						coerce, ZX, ZXD, QX, QxD, QxY);
		factor0(a, c1, c2, factorDecomp L);
	}

	local factor3(a:%, L:ZXD, c1:QX, c2:Z):% == {
		import from Q;
		import from ThirdOrderLinearOrdinaryRecurrenceSolver(Z, Q,
						coerce, ZX, ZXD, QX, QxD, QxY);
		factor0(a, c1, c2, factorDecomp L);
	}

	local factor0(a:%, c1:QX, c2:Z, factL:FACLODO):% == {
		import from I, Z, Q, Qx, QxY, QxD, V QxD, RATRED, ALGRED;
		factL case rat => {
			rec := factL.rat;
			v := rec.rat;
			one?(n := #v) => { assert(one?(rec.mode)); a }	-- irr
			m := rec.mode;
			if m = 1 or m = 3 or m = 4 then
				v.1 := inv((c2 * c1)::Qx) * v.1;
			w:V QxD := zero next n;
			w.1 := m::Z::QxD;
			for i in 1..n repeat w(next i) := v.i;
			per [w];
		}
		algrec := factL.alg;
		m := algrec.mode;
#if LATER_WHEN_V(QxY)_IS_IN_REP
		md := prev(-m)::Z::QxY;
		h := algrec.modulus::Qx::QxY;
		unum := numerator(algrec.c0);
		uden := denominator(algrec.c0);
#else
		md := prev(-m)::Z::QxD;
		h := algrec.modulus::Qx::QxD;
		unum := QxY2QxD numerator(algrec.c0);
		uden := QxY2QxD denominator(algrec.c0);
#endif
		zero? #(v := algrec.ratpart) => {
			assert(zero? m);
			per [[md, h, unum, uden]];
		}
		assert(m = 0 or m = 3 or m = 4);
		if ~zero?(m) then v.1 := inv((c2 * c1)::Qx) * v.1;
#if LATER_WHEN_V(QxY)_IS_IN_REP
		v1 := QxD2QxY(v.1);
#else
		v1 := v.1;
#endif
		m = 4 => {
			assert(#v = 2);
#if LATER_WHEN_V(QxY)_IS_IN_REP
			v2 := QxD2QxY(v.2);
#else
			v2 := v.2;
#endif
			per [[md, h, unum, uden, v1, v2]];
		}
		assert(#v = 1);
		per [[md, h, unum, uden, v1]];
	}

	local lodoSections(a:QxD, n:Z):%	== {
		import from ZXD, Array ZXD;
		per [[makefrac(QXD, QxD, ZXD2QXD f)
			for f in sections(makez makepoly(QXD,QxD,a),n)]$V(QxD)];
	}

	system(n:I, l:List %):Partial % == {
		import from Boolean, Partial Qx;
		(square?, m) := nthRoot(n, 2);
		~square? => failed;
		A:M Qx := zero(m, m);
		for i in 1..m repeat for j in 1..m repeat {
			failed?(u := frac first l) => return failed;
			A(i, j) := retract u;
			l := rest l;
		}
		[A::%];
	}

	system(a:%):Partial % == {
		import from I, Z, Qx, QxD, M Qx, List %;
		lodo? a => {
			zero?(L := lodo a) or zero? degree L => system(0,empty);
			[(transpose companion lodonormal L)::%];
		}
		failed;
	}

	eigenring(a:%):Partial % == {
		import from Partial M Qx;
		lodo? a => [per [eigen lodo a]];
		mat? a => [eigen(mat a)::%];
		failed;
	}

	local eigen(a:QxD):V QxD == {
		import from I, Q, ZX, Qx, V ZX, V QXD,
		   LinearOrdinaryRecurrenceEigenring(Z,Q,coerce,ZX,ZXD,QX,QXD);
		import from RATSOL(Z, Q, coerce, ZX, ZXD, QX);
		import from UAF(Z, ZX, Q, QX), UAF(QX, QXD, Qx, QxD);
		-- TEMPO: USE matrix eigenring, which is faster for differences
		(d, ignore, num) := matrixEigenring makez makepoly(QXD, QxD, a);
		-- (den, dvec, num) := eigenring makez makepoly(QXD, QxD, a);
		v:V QxD := zero(n := #num);
		if n > 0 then {
			-- d := factorialExpansion den;
			for i in 1..n repeat {
				-- v.i := inv(makeRational(d*dvec.i)::Qx) * num.i;
				v.i := inv(makeRational(d)::Qx) * num.i;
			}
		}
		v;
	}

	local eigen(A:M Qx):M Qx == {
		import from I, Q, Qx, QFX, M QFX, V M QFX, UAF(Z, ZX, Q, QX);
		import from SYSSOL(Z, Q, coerce, ZX, ZXD, QX);
		import from LinearOrdinaryFirstOrderSystem ZX;
		assert(square? A);
		(den, num) := eigenring system MQx2MZx A;
		dim := #num;
		d:QX := { dim > 0 => makeRational den; 0 }
		n := numberOfRows A;
		m:M Qx := zero(n, n * dim);
		for k in 1..dim repeat {
			c := prev(k) * n;
			for i in 1..n repeat for j in 1..n repeat
			m(i, j + c) := expand(num(k)(i, j)) / d;
		}
		m;
	}

	adjoint(a:%):Partial % == {
		lodo? a => [adjoint(lodo a)::%];
		mat? a => [(- transpose(mat a))::%];
		failed;
	}

	local sprd(a:ZX):% == {
		import from Z, List Z;
		per [[n::QxD for n in integerDistances(a) | n >= 0]$V(QxD)];
	}

	local sprd(a:ZX, b:ZX):% == {
		import from Z, List Z;
		per [[n::QxD for n in integerDistances(a, b) | n >= 0]$V(QxD)];
	}

	local polynz(a:%, f:ZX -> %):Partial % == {
		import from Z, QX, Qx, QxD, UAF(Z, ZX, Q, QX);
		lodo? a  => {
			zero?(la := lodo a) => failed;
			zero?(degree la) => {
				fa := leadingCoefficient la;
				one?(denominator fa) => {
					(c, p) := makeIntegral numerator fa;
					[f p];
				}
				failed;
			}
			failed;
		}
		failed;
	}

	local polynz(a:%, b:%, f:(ZX, ZX) -> %):Partial % == {
		import from Z, QX, Qx, QxD, UAF(Z, ZX, Q, QX);
		lodo? a and lodo? b => {
			zero?(la := lodo a) or zero?(lb := lodo b) => failed;
			zero?(degree la) and zero?(degree lb) => {
				fa := leadingCoefficient la;
				fb := leadingCoefficient lb;
				one?(denominator fa) and one?(denominator fb)=>{
					(c, pa) := makeIntegral numerator fa;
					(c, pb) := makeIntegral numerator fb;
					[f(pa, pb)];
				}
				failed;
			}
			failed;
		}
		failed;
	}

	rationalSolution(a:%, b:%):Partial % == {
		import from Z, QX, Qx, QxD;
		lodo? a and lodo? b and (zero?(l:=lodo b) or zero? degree l) =>
				[per [ratsol(lodo a, leadingCoefficient l)]];
		failed;
	}

	local ratsol(a:QxD, q:Qx):V QxD == {
		import from Q, QX, QFX, Partial QFX, QxD;
		import from RATSOL(Z, Q, coerce, ZX, ZXD, QX);
		import from UAF(Z, ZX, Q, QX), UAF(QX, QXD, Qx, QxD);
		(d, opp) := makeIntegral a;	-- opp = d * a is in Q[x][D]
		(l, op) := makez0 opp;		-- op = l * d * a is in Z[x][D]
		(den, num) := particularSolution(op, Qx2Zx((l::Q) * d * q));
		failed? num => empty;				-- no solution
		[(expand(retract num) / makeRational(den))::QxD]
	}

	polynomialSolution(a:%, b:%):Partial % == {
		import from Z, QX, Qx, QxD;
		lodo? a and lodo? b and (zero?(l:=lodo b) or zero? degree l) =>
				[per [polsol(lodo a, leadingCoefficient l)]];
		failed;
	}

	local polsol(a:QxD, f:Qx):V QxD == {
		import from Z, Q, QX, QFX, Partial QFX, QXD, QxD;
		import from LinearOrdinaryOperatorPolynomialSolutions(Z, Q,_
							coerce, ZX, ZXD, QFX);
		import from UAF(QX, QXD, Qx, QxD);
		TRACE("multlodo::polsol: a = ", a);
		TRACE("multlodo::polsol: f = ", f);
		(d, opp) := makeIntegral a;	-- opp = d a is in Q[x][D]
		f := d * f;			-- new eq is: opp(y) = f
		degree(df := denominator f) > 0 => empty;	-- no solution
		(l, op) := makez0(df * opp);	-- op = l df d a is in Z[x][D]
		-- TRACE("multlodo::polsol: op = ", op);
		u := particularSolution(op, ((l::Q) * numerator f)::QFX);
		failed? u => empty;				-- no solution
		[expand(retract u)::Qx::QxD]
	}

	liouvillianSolution(a:%):Partial % == {
		lodo? a => [per [liouvillianSolution lodo a]];
		failed;
	}

	hyper(a:%):Partial % == {
		import from I, V QxD;
		lodo? a => {
			empty?(v := hyper lodo a) => [per [v]];
			[per [v.1]];
		}
		failed;
	}

	kernel(a:%):Partial % == {
		import from QX, Partial M Qx;
		lodo? a => [per [kernel lodo a]];
		mat? a => [per [kernel(mat a)]];
		failed;
	}

	local fracgcd(a:Qx, b:Qx):Partial % == {
		import from QX;
		fracpoly(a, b, gcd);
	}

	local fraclcm(a:Qx, b:Qx):Partial % == {
		import from QX;
		fracpoly(a, b, lcm);
	}

	degree(a:%):Partial % == {
		lodo? a => lododegree lodo a;
		failed;
	}

	local vectorize(L:QxD):V QxD == {
		import from I;
		v:V QxD := zero 1;
		v.1 := L;
		v;
	}

	element(a:%, b:%):Partial % == {
		import from Boolean, I, Z, Partial Z, Qx;
		~(vec? a) or failed?(u := integer b) => failed;
		[elt(vec a, machine retract u)];
	}

	local elt(a:V QxD, n:I):% == {
		n < 1 or n > #a => 0;
		(a.n)::%;
	}

	coefficient(a:%, b:%):Partial % == {
		import from Boolean, Z, Partial Z, Qx;
		(~lodo? a) or failed?(u := integer b) => failed;
		coeff(lodo a, retract u);
	}

	local coeff(a:QxD, n:Z):Partial % == {
		zero? a or n < 0 => [0];
		zero?(d := degree a) => fraccoeff(leadingCoefficient a, n);
		[coefficient(a, n)::QxD::%];
	}

	local fraccoeff(a:Qx, n:Z):Partial % == {
		import from QX;
		assert(n >= 0);
		zero? degree denominator a =>
			[coefficient(numerator a, n)::QX::%];
		failed;
	}
		
	local lododegree(a:QxD):Partial % == {
		import from Z;
		zero?(d := degree a) => fracdegree leadingCoefficient a;
		[d::%];
	}

	local fracdegree(a:Qx):Partial % == {
		import from Z, QX;
		zero? degree denominator a => [degree(numerator a)::%];
		failed;
	}

	local fracpoly(a:Qx, b:Qx, f:(QX, QX) -> QX):Partial % == {
		import from Z, QX;
		zero? degree denominator a and zero? degree denominator b =>
			[f(numerator a, numerator b)::%];
		failed;
	}

	shift(a:%, b:%):Partial % == {
		import from Z, Partial Z, Qx, Partial Qx;
		failed?(ua := frac a) or failed?(ub := integer b) => failed;
		[shift(retract ua, retract ub)::QxD::%];
	}

	local shift(a:Qx, n:Z):Qx == {
		import from QX;
		zero? n => a;
		xpn:QX := monom$QX + n::QX;
		compose(numerator a, xpn) / compose(denominator a, xpn);
	}

	apply(a:%, b:%):Partial % == {
		import from Z;
		lodo? a and lodo? b and (zero?(q:=lodo b) or zero? degree q) =>
				[(lodo(a)(leadingCoefficient q))::QxD::%];
		failed;
	}

	(a:%) = (b:%):Boolean == {
		import from V QxD, M Qx;
		lodo? a => lodo? b and lodo a = lodo b;
		vec? a => vec? b and vec a = vec b;
		mat? a => mat? b and mat a = mat b;
		never;
	}

	extree(a:%):ExpressionTree == {
		import from V QxD, M Qx;
		lodo? a => extree lodo a;
		vec? a => extree vec a;
		mat? a => extree mat a;
		never;
	}

	(a:%) + (b:%):Partial % == {
		lodo? a and lodo? b => [(lodo a + lodo b)::%];
		mat? a and mat? b => [(mat a + mat b)::%];
		failed;
	}

	(a:%) * (b:%):Partial % == {
		lodo? a and lodo? b => [(lodo a * lodo b)::%];
	 	mat? a and mat? b => [(mat a * mat b)::%];
		failed;
	}

	(a:%) / (b:%):Partial % == {
		import from Boolean, Z, Qx;
		lodo? a and lodo? b and (~zero?(q := lodo b)) => {
			p := lodo a;
			zero? degree q =>
				[(inv(leadingCoefficient q) * lodo a)::%];
			[rightQuotient(p, q)::%];
		}
		failed;
	}

	-- returns [a] if a is in Qx, failed otherwise
	local frac(a:%):Partial Qx == {
		import from Boolean, Z, QxD, Qx;
		~lodo? a => failed;
		p := lodo a;
		zero? p or zero? degree p => [leadingCoefficient p];
		failed;
	}

	-- returns [a] if a is in Integer, failed otherwise
	integer(a:%):Partial Z == {
		import from Z, Q, QX, Qx, Partial Qx;
		failed?(u := frac a) => failed;
		f := retract u;
		degree(n := numerator f) > 0
			or degree(d := denominator f) > 0 => failed;
		q := leadingCoefficient(n) / leadingCoefficient(d);
		denominator(q) = 1 => [integer numerator q];
		failed;
	}

	(a:%)^(b:%):Partial % == {
		import from I, Z, Partial Z, Qx, Partial Qx, M Qx;
		failed?(u := integer b) => failed;
		(n := retract u) < 0 => {
			failed?(ua := frac a) => failed;
			[(retract(ua)^n)::QxD::%];
		}
		lodo? a => [(lodo(a)^n)::%];
		mat? a => [(mat(a)^(machine n))::%];
		failed;
	}

	local lodolcm(a:%, b:%, lodoop:(QxD, QxD) -> QxD):Partial % == {
		import from Z;
		lodo? a and lodo? b => {
			zero?(p := lodo a) or zero?(q := lodo b) => [0];
			zero? degree p and zero? degree q =>
			    fraclcm(leadingCoefficient p, leadingCoefficient q);
			[lodonormal(lodoop(p, q))::%];
		}
		failed;
	}

	local lodogcd(a:%, b:%, lodoop:(QxD, QxD) -> QxD):Partial % == {
		import from Z;
		lodo? a and lodo? b => {
			zero?(p := lodo a) => [b];
			zero?(q := lodo b) => [a];
			zero? degree p and zero? degree q =>
			    fracgcd(leadingCoefficient p, leadingCoefficient q);
			[lodonormal(lodoop(p, q))::%];
		}
		failed;
	}

	local makefrac(QxT:MonogenicAlgebra Qx,_
		ZxT:MonogenicAlgebra Zx, p:ZxT, nrm?:Boolean):QxT =={
		import from Zx, Qx;
		zero? p => 0;
		lcp := leadingCoefficient p;
		local lcq:Qx;
		local lc1:Zx;
		if nrm? then { lcq := 1; lc1 := inv lcp; }
			else { lcq := Zx2Qx lcp; lc1 := 1 }
		q:QxT := term(lcq, degree p);
		for term in reductum p repeat {
			(c, n) := term;
			q := add!(q, Zx2Qx(c * lc1), n);
		}
		q;
	}

	local ZXD2QXD(a:ZXD):QXD == {
		import from UAF(Z, ZX, Q, QX);
		op:QXD := 0;
		for term in a repeat {
			(p, n) := term;
			op := add!(op, makeRational p, n);
		}
		op;
	}

	local lodonpos(a:%, b:%, min:Z, f:(QxD,Z)->%):Partial % == {
		import from Boolean, Z, Partial Z;
		TRACE("lodonpos:a = ", a);
		TRACE("lodonpos:b = ", b);
		TRACE("lodonpos:min = ", min);
		(~lodo? a) or failed?(u := integer b)
			or (n := retract u) < min => failed;
		TRACE("lodonpos: ", "input ok, calling f");
		[f(lodo a, n)];
	}

	local lodopos(a:%, b:%, f:(QxD, Z) -> QxD):Partial % == {
		import from Z;
		lodonpos(a, b, 1, (L:QxD, n:Z):% +-> f(L, n)::%);
	}

	local extpow(a:QxD, n:Z):QxD == {
		import from ZXD;
		makefrac(QXD, QxD,
			ZXD2QXD exteriorPower(makez makepoly(QXD, QxD, a), n));
	}

	makeIntegral(a:%):Partial % == {
		lodo? a => [makefrac(QXD, QxD, makepoly(QXD,QxD,lodo a))::%];
		failed;
	}

	normalize(a:%):Partial % == {
		import from I, V QxD;
		lodo? a => [lodonormal(lodo a)::%];
		vec? a => [per [vecnormal! copy vec a]];
		failed;
	}

	local lodonormal(a:QxD):QxD == {
		import from Z, Qx;
		zero? a => a;
		c := leadingCoefficient a;
		zero? degree a => fracnormal(c)::QxD;
		inv(c) * a;
	}

	local fracnormal(a:Zx):Qx ==
		polynormal numerator a / polynormal denominator a;

	local polynormal(a:ZX):QX == {
		import from UAF(Z, ZX, Q pretend FractionFieldCategory Z, QX);
		(c, b) := normalize a;
		b;
	}

	local fracnormal(a:Qx):Qx ==
		polynormal numerator a / polynormal denominator a;

	local polynormal(a:QX):QX == {
		import from Z, Q;
		zero? a or zero? degree a => a;
		inv(leadingCoefficient a) * a;
	}

	local makefrac(QXT:MonogenicAlgebra QX,_
		QxT:MonogenicAlgebra Qx, a:QXT):QxT == {
		import from UAF(QX, QXT, Qx, QxT);
		makeRational a;
	}

	local makepoly(QXT:MonogenicAlgebra QX,_
		QxT:MonogenicAlgebra Qx, a:QxT):QXT == {
		import from UAF(QX, QXT, Qx, QxT);
		(c, b) := makeIntegral a;
		b;
	}

	local makez(a:QXD):ZXD == {
		(c, L) := makez0 a;
		L;
	}

	local coeff(c:Z, n:Z):Z == c;
	local makez0(a:QXD):(Z, ZXD) == {
		import from Z, ZX, List Z;
		import from UAF(Z, ZX, Q, QX);
		op:ZXD := 0;
		d:ZX := 0;
		TRACE("makez0: a = ", a);
		for term in a repeat {
			(p, n) := term;
			(c, q) := makeIntegral p;	-- p = q / c
			op := add!(op, q, n);
			d := add!(d, c, n);
		}
		-- op = sum q_i D^i, d = sum c_i X^i, a = sum (q_i / c_i) D^i
		l := lcm [coeff term for term in d];
		L:ZXD := 0;
		for term in op for zterm in d repeat {
			(q, n) := term;
			(c, m) := zterm;
			assert(n = m);
			L := add!(L, quotient(l, c) * q, n);	-- L = l * a
		}
		(l, L);
	}

	local MQx2MZx(A:M Qx):M Zx == {
		import from I;
		(r, c) := dimensions A;
		B:M(Zx) := zero(r, c);
		for i in 1..r repeat for j in 1..c repeat
			B(i, j) := Qx2Zx A(i, j);
		B;
	}

	local Zx2Qx(f:Zx):Qx == {
		import from UAF(Z, ZX, Q, QX);
		makeRational(numerator f) / makeRational(denominator f);
	}

	local Qx2Zx(f:Qx):Zx == {
		import from ZX, UAF(Z, ZX, Q, QX);
		(a, n) := makeIntegral numerator f;	-- num(f) = n/a
		(b, d) := makeIntegral denominator f;	-- den(f) = d/b
		(b * n) / (a * d);
	}

	local liouvillianSolution(a:QxD):V QxD == {
		import from Q, V Qx, QxD;
		import from LinearOrdinaryRecurrenceLiouvillianSolutions(Z,_
							Q, coerce, ZX, ZXD, QX);
		opq := makepoly(QXD, QxD, a);
		op := makez opq;
		[f::QxD for f in liouvillianSolution op];
	}

	local hyper(a:QxD):V QxD == {
		import from Q, Partial Qx, QxD;
		import from LinearOrdinaryRecurrenceHypergeometricSolutions(Z,_
							Q, coerce, ZX, ZXD, QX);
		opq := makepoly(QXD, QxD, a);
		op := makez opq;
		failed?(u := hypergeometricSolution op) => empty;
		[retract(u)::QxD];
	}

	local kernel(a:QxD):V QxD == {
		import from Z, Q, V QX, Qx, QFX, Vector QFX;
		import from RATSOL(Z, Q, coerce, ZX, ZXD, QX);
		TRACE("multlodo::kernel, a = ", a);
		opq := makepoly(QXD, QxD, a);
		-- TRACE("multlodo::kernel, opq = ", opq);
		vecnormal kernel makez opq;
	}

	local kernel(a:M Qx):M Qx == {
		import from Q, LinearOrdinaryFirstOrderSystem ZX;
		import from SYSSOL(Z, Q, coerce, ZX, ZXD, QX);
		matnormal kernel system MQx2MZx a;
	}

	local maxdeg(v:V QX):Z == {
		import from Boolean, QX;
		n:Z := 0;
		for p in v repeat
			if ~zero?(p) and (d := degree p) > n then n := d;
		n;
	}

	local matnormal(den:ZX, v:M QFX):M Qx == {
		import from I, QFX, Qx, UAF(Z, ZX, Q, QX);
		d := makeRational den;
		(r, c) := dimensions v;
		w:M Qx := zero(r, c);
		for i in 1..r repeat for j in 1..c repeat
			w(i, j) := expand(v(i, j))/d;
		w;
	}

	local vecnormal(den:ZX, v:V QFX):V QxD == {
		import from I, QFX, Qx, UAF(Z, ZX, Q, QX);
		d := makeRational den;
		w:V QxD := zero(n := #v);
		for i in 1..n repeat w.i := fracnormal(expand(v.i)/d)::QxD;
		w;
	}

	local vecnormal(v:V Qx):V QxD == {
		import from I;
		w:V QxD := zero(n := #v);
		for i in 1..n repeat w.i := fracnormal(v.i)::QxD;
		w;
	}

	local vecnormal(v:V Zx):V QxD == {
		import from I;
		w:V QxD := zero(n := #v);
		for i in 1..n repeat w.i := fracnormal(v.i)::QxD;
		w;
	}

	local vecnormal!(v:V QxD):V QxD == {
		import from I;
		for i in 1..#v repeat v.i := lodonormal(v.i);
		v;
	}
}
