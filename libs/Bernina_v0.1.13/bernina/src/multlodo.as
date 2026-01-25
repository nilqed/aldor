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
-- Copyright (c) Manuel Bronstein 1994-2001
-- Copyright (c) INRIA 1997-2001, Version 0.1.13
-- Logiciel Bernina (c) INRIA 1997-2001, dans sa version 0.1.13
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1994-1997
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I	== MachineInteger;
	Z	== Integer;
	Q	== Fraction Z;
	PZX	== Product ZX;
	PQX	== Product QX;
	FpX	== DenseUnivariatePolynomial Fp;
	FpXD	== LinearOrdinaryDifferentialOperator FpX;
	Zx	== Fraction ZX;
	Qx	== Fraction QX;
	Qxy	== Fraction QxY;
	QXy	== SparseUnivariatePolynomial QX;
	QXD	== LinearOrdinaryDifferentialOperator QX;
	ZXD	== LinearOrdinaryDifferentialOperator ZX;
	ZXE	== LinearOrdinaryRecurrence(Z, ZX);
	ZxD	== LinearOrdinaryDifferentialOperator Zx;
	SYS	== LinearOrdinaryFirstOrderSystem;
	ZxY	== DenseUnivariatePolynomial Zx;
	QxYZ	== DenseUnivariatePolynomial QxY;
	HEQ	== LinearHolonomicDifferentialEquation(Z, Q, coerce, ZX, ZXD);
	V	== Vector;
	M	== DenseMatrix;
	UAF	== MonogenicAlgebraOverFraction;
	RATRED	== Record(mode:I, rat: V QxD);
	ALGRED	== Record(mode:I, modulus:QX, c0:Qxy, ratpart:V QxD);
	FACLODO	== Union(rat: RATRED, alg: ALGRED);
	ALGRIC	== Record(modulus:QX, den:QxY, num:QxYZ);
	IRRSOL2	== Record(grp:I, exp:Qx, const:Q, pullback:Qx);
	SOL2	== Union(red:List QxY, irr:IRRSOL2);
	SOLUTION== Union(ratric:QxY, algric:ALGRIC, inv:INVAR, radinv:RINVAR);
	EIGEN	== LinearOrdinaryDifferentialEigenring;
	MODSOL	== LinearOrdinaryOperatorModularPolynomialSolutions(Z,_
						 Q, coerce, ZX, ZXD, QX, QXD);
	RATSOL	== LinearOrdinaryDifferentialOperatorRationalSolutions(Z,_
						 Q, coerce, ZX, ZXD, QX);
	INVAR	== LinearOrdinaryDifferentialOperatorInvariants(Z,_
						 Q, coerce, ZX, ZXD, QX);
	RINVAR	== LinearOrdinaryDifferentialOperatorRadicalInvariants(Z,_
						 Q, coerce, ZX, ZXD, QX);
	SINVAR	== LinearOrdinaryDifferentialOperatorSemiInvariants(Z,_
						 Q, coerce, ZX, ZXD, QX);
	EXTKER	== LinearOrdinaryDifferentialOperatorExteriorKernel(Z,_
							Q, coerce, ZX, ZXD, QX);
	ORDER2	== SecondOrderLinearOrdinaryDifferentialSolver(Z, Q,_
						coerce, ZX, ZXD, QX, QxD, QxY);
	ORDER3	== ThirdOrderLinearOrdinaryDifferentialSolver(Z, Q,_
						coerce, ZX, ZXD, QX, QxD, QxY);
}

MultiLodo(ZX:UnivariatePolynomialCategory Z,
	QX:UnivariatePolynomialCategory Q,
	QxD:LinearOrdinaryDifferentialOperatorCategory Qx,
	QxY:UnivariatePolynomialCategory Qx): PartialRing with {
		adjoint: % -> Partial %;
#if ALDOC
\alpage{adjoint}
\Usage{\name~L}
\Params{ {\em L} & $\weyl$ & A differential operator\\ }
\Retval{
Returns the adjoint operator of $L$, \ie
$$
L^\ast = \sum_{i=0}^n (-1)^i \frac{d^i}{dx^i}\cdot a_i
$$
where
$$
L = \sum_{i=0}^n a_i \frac{d^i}{dx^i}
$$
and $\cdot$ is the product in $\weyl$.
}
\begin{alex}
It can happen that $L^\ast$ has a nontrivial rational kernel, while
$L$ has a trivial one:
\begin{ttyout}
1 --> L := x*D^3 + D^2 - x^2*D - 2*x;
2 --> LL := adjoint(L);
3 --> tex(LL);
\end{ttyout}
$$
-x\,D^{3}-2\,D^{2}+x^{2}\,D
$$
So $L^\ast 1 = 0$, while $L y = 0$ has no nonzero rational solution:
\begin{ttyout}
4 --> K := kernel(L);
5 --> tex(K);
\end{ttyout}
$$
[~]
$$
We also verify that $L^{\ast\ast} = L$:
\begin{ttyout}
6 --> tex(L - adjoint(LL));
\end{ttyout}
$$
0
$$
\end{alex}
#endif
		allRationalExponents?: % -> Partial %;
		apply: (%, %) -> Partial %;
#if ALDOC
\alpage{apply}
\Usage{\name(L, f)}
\Params{
{\em L} & $\weyl$ & A differential operator\\
{\em f} & $\QQ(x)$ & A rational function\\
}
\Retval{Returns $L(f)$.}
\begin{alex}
We can verify that an element is in the kernel of an operator by applying
the operator to it:
\begin{ttyout}
1 --> L := (x^9+x^3)*D^3 + 18*x^8* D^2 - 90*x*D -30*(11*x^6-3);
2 --> K := kernel(L);
3 --> f := element(K, 1);
4 --> tex(f);
\end{ttyout}
$$
{{x} \over {x^{6}+1}}
$$
\begin{ttyout}
5 --> tex(apply(L, f));
\end{ttyout}
$$
0
$$
\end{alex}
\alseealso{\alexp{diff}}
#endif
		coerce: QX -> %;
		coerce: QxD -> %;
		coerce: M Qx -> %;
		coerce: M QxY -> %;
		coefficient: (%, %) -> Partial %;
#if ALDOC
\alpage{coefficient}
\Usage{\name(L, n)\\ \name(p, n)}
\Params{
{\em L} & $\weyl$ & A differential operator\\
{\em p} & $\QQ[x]$ & A polynomial\\
{\em n} & $\ZZ$ & An exponent\\
}
\Retval{Returns the coefficient of $\frac{d^n}{dx^n}$ in $L$ or the
coefficient of $x^n$ in $p$.}
\alseealso{\alexp{degree}}
#endif
		Darboux: % -> Partial %;
#if ALDOC
\alpage{Darboux}
\Usage{\name~L}
\Params{
{\em L} & $\weyl$ & A second order differential operator\\
}
\Retval{
\name(L) returns Darboux polynomials for $L$ of lowest possible degree.
Note that $y = e^{\int u dx}$ is a solution of $L y = 0$
if and only if $p(x,u) = 0$ for some Darboux polynomial $p$.
}
\Remarks{
If \name(L) returns $[]$, then this proves that $L$ is irreducible and has no
nontrivial Darboux curves, and hence that $L y = 0$ has no Liouvillian
solution.
}
\begin{alex}
To look for closed-form solutions of the differential equation
\begin{equation}
\label{eq:exdarboux}
\frac{d^2 y}{dx^2} +
\paren{\frac 3{16 x^2} + \frac 2{9 (x-1)^2} - \frac 3{16 x (x-1)}} y = 0
\end{equation}
we look for a Darboux polynomial as follows:
\begin{ttyout}
1 --> L := D^2 + 3/16/x^2 + 2/9/(x-1)^2 - 3/(16*x*(x-1));  
2 --> v := Darboux(L);
3 --> tex(v);
\end{ttyout}
\begin{eqnarray*}
[ u^{6}&+&{{-4\,x+2} \over {x^{2}-x}}\,u^{5}+
{{{{20} \over {3}}\,x^{2}-{{105} \over {16}}\,x+
  {{25} \over {16}}} \over {x^{4}-2\,x^{3}+x^{2}}}\,u^{4}\\
&+& {{-{{160} \over {27}}\,x^{3}+
  {{3725} \over {432}}\,x^{2}-{{65} \over {16}}\,x+{{5} \over {8}}}
     \over {x^{6}-3\,x^{5}+3\,x^{4}-x^{3}}}\,u^{3}\\
&+& {{{{80} \over {27}}\,x^{4}-{{1225} \over {216}}\,x^{3}+
 {{27425}\over {6912}}\,x^{2}-{{155} \over {128}}\,x+{{35} \over {256}}}
     \over {x^{8}-4\,x^{7}+6\,x^{6}-4\,x^{5}+x^{4}}}\,u^{2}\\
&+& {{-\left({{64} \over {81}}\,x^{5}\right)+{{605} \over {324}}\,x^{4}-
 {{11927} \over {6912}}\,x^{3}+{{301} \over {384}}\,x^{2}-
   {{45} \over {256}}\,x+{{1} \over {64}}} \over
     {x^{10}-5\,x^{9}+10\,x^{8}-10\,x^{7}+5\,x^{6}-x^{5}}}\,u\\
&+&{{{{64} \over {729}}\,x^{6}-{{359} \over {1458}}\,x^{5}+
  {{105251} \over {373248}}\,x^{4}-{{6251} \over {36864}}\,x^{3}+
    {{2089} \over {36864}}\,x^{2}-{{41} \over {4096}}\,x+{{3} \over
      {4096}}} \over {x^{12}-6\,x^{11}+15\,x^{10}-20\,x^{9}+15\,x^{8}-
        6\,x^{7}+x^{6}}} ]
\end{eqnarray*}
This means that~(\ref{eq:exdarboux}) has a solution $y(x)$ whose logarithmic
derivative is a root of the above polynomial.
\end{alex}
\begin{maplerem}
When using \name~from inside \maple, you must give the symbol for the
returned curves as an extra argument. So the above example in \maple{}
would be:
\begin{ttyout}
> L := D^2 + 3/16/x^2 + 2/9/(x-1)^2 - 3/(16*x*(x-1));  
> Darboux(L, D, x, u);
\end{ttyout}
\begin{eqnarray*}
\left[ \left ({x}^{12}\right.\right.
&-&\left. 6\,{x}^{11}+15\,{x}^{10}-20\,{x}^{9}+15\,{x}^{8}-6\,{
x}^{7}+{x}^{6}\right ){u}^{6}\\
&+&
\left (-4\,{x}^{11}+22\,{x}^{10}-50\,{x}
^{9}+60\,{x}^{8}-40\,{x}^{7}+14\,{x}^{6}-2\,{x}^{5}\right ){u}^{5}\\
&+&
\left ({\frac {20}{3}}\,{x}^{10}-{\frac {1595}{48}}\,{x}^{9}+{\frac {
1085}{16}}\,{x}^{8}-{\frac {1735}{24}}\,{x}^{7}+{\frac {1015}{24}}\,{x
}^{6}-{\frac {205}{16}}\,{x}^{5}+{\frac {25}{16}}\,{x}^{4}\right ){u}^
{4}\\
&+&
\left (-{\frac {160}{27}}\,{x}^{9}+{\frac {11405}{432}}\,{x}^{8}-{
\frac {1145}{24}}\,{x}^{7}+{\frac {9635}{216}}\,{x}^{6}-{\frac {1225}{
54}}\,{x}^{5}+{\frac {95}{16}}\,{x}^{4}-5/8\,{x}^{3}\right ){u}^{3}\\
&+&
\left ({\frac {80}{27}}\,{x}^{8}-{\frac {835}{72}}\,{x}^{7}+{\frac {
126305}{6912}}\,{x}^{6}-{\frac {2845}{192}}\,{x}^{5}+{\frac {22555}{
3456}}\,{x}^{4}-{\frac {95}{64}}\,{x}^{3}+{\frac {35}{256}}\,{x}^{2}
\right ){u}^{2}\\
&+&
\left (-{\frac {64}{81}}\,{x}^{7}+{\frac {287}{108}}\,{x}^{6}
-{\frac {74501}{20736}}\,{x}^{5}+{\frac {17345}{6912}}\,{x}^{4}
-{\frac {737}{768}}\,{x}^{3}+{\frac {49}{256}}\,{x}^{2}
-{\frac {1}{64}}\,x\right )u\\
&+&
\left.
{\frac {64}{729}}\,{x}^{6}-{\frac {359}{1458}}\,{x}^{5}+
{\frac {105251}{373248}}\,{x}^{4}-{\frac {6251}{36864}}\,{x}^{3}+{
\frac {2089}{36864}}\,{x}^{2}-{\frac {41}{4096}}\,x+{\frac {3}{4096}} \right]
\end{eqnarray*}
\end{maplerem}
#endif
		decompose: % -> Partial %;
#if ALDOC
\alpage{decompose}
\Usage{\name~L}
\Params{ {\em L} & $\weyl$ & A differential operator of order at most 3\\ }
\Descr{Returns one of the following possible results:
\begin{itemize}
\item[(i)] \emph{L}, in which case \emph{L} cannot be written as a
least common left multiple of lower order operators
(\emph{L} can still be either reducible or irreducible in that case).
\item[(ii)] $[L_1,\dots,L_n]$ where $L_i \in \weylq$, in which case
\emph{L} is a least common left multiple of $L_1,\dots,L_n$.
\item[(iii)] $[h(x),a(x,u),b(x,u),f_1(x,u),\dots,f_n(x,u)]$,
where $h(x) \in \QQ[x]$ is irreducible and $a(x,u)$,\\
$b(x,u)$,$f_1(x,u),\dots,f_n(x,u) \in \QQ(x)[u]$,
in which case \emph{L} is a least common left multiple of
$f_1(x,D),\dots,f_n(x,D)$ and of $D + a(\alpha, x) / b(\alpha, x)$
where $\alpha$ ranges over all the roots of $h(x)$.
\end{itemize}
}
\begin{alex}
We decompose the differential equation
\begin{equation}
\label{eq:exdecompose}
\frac{d^3 y}{dx^3} - \frac{x^2+3}x \frac{d^2 y}{dx^2} -
\frac{2x^4-x^2-3}{x^2} \frac{dy}{dx} + 2x^3 y = 0
\end{equation}
as follows:
\begin{ttyout}
1 --> L := D^3-(x^2+3)/x*D^2-(2*x^4-x^2-3)/x^2*D + 2*x^3;
2 --> v := decompose(L);
3 --> tex(v);
\end{ttyout}
$$
\left[ x^{2}+4\,x+2 , \left(-x-2\right)\,u , 1 , u-x \right]
$$
This means that the operator of~(\ref{eq:exdecompose}) is a least
common left multiple of $d/dx - x$, $d/dx - (\alpha+2) x$
and $d/dx - (\beta+2) x$ where $\alpha$ and $\beta$ are the
two roots of $x^2 + 4 x + 2 = 0$. Since $\alpha = -2 - \sqrt 2$
and $\beta = -2 + \sqrt 2$, our operator is a least
common left multiple of $d/dx - x$, $d/dx + x \sqrt 2$
and $d/dx - x \sqrt 2$.
\end{alex}
\begin{maplerem}
When using \name~from inside \maple, the result returned from
\bernina{} is further transformed into one of the following:
\begin{itemize}
\item[(i)] \emph{L}, in which case \emph{L} cannot be written as a
least common left multiple of lower order operators.
\item[(ii)] An object of the form {\tt LeftLcm}$(L_1,\dots,L_n)$
where the $L_i$'s are differential operators, in which case
\emph{L} is a least common left multiple of $L_1,\dots,L_n$.
\item[(iii)] An object of the form {\tt LeftLcm}$(L_\alpha, and~conjugates)$
where $L_\alpha$ is a differential operator containing an algebraic
number $\alpha$, in which case
\emph{L} is a least common left multiple of all the conjugates of $L_\alpha$.
\end{itemize}
So the above example in \maple{} would be:
\begin{ttyout}
> L := D^3-(x^2+3)/x*D^2-(2*x^4-x^2-3)/x^2*D + 2*x^3;
> decompose(L, D, x);
\end{ttyout}
$$
{\it LeftLcm}(D-\sqrt {2}x,D+\sqrt {2}x,D-x)
$$
\end{maplerem}
\alseealso{\alexp{factor},\alexp{Loewy}}
#endif
		degree: % -> Partial %;
#if ALDOC
\alpage{degree}
\Usage{\name~L\\ \name~p}
\Params{
{\em L} & $\weyl$ & A differential operator\\
{\em p} & $\QQ[x]$ & A polynomial\\
}
\Retval{Returns the degree of $L$ in $\frac d{dx}$ or the degree of $p$ in $x$.}
\alseealso{\alexp{coefficient}}
#endif
		D: (%, %) -> Partial %;
#if ALDOC
\alpage{diff}
\Usage{\name~f\\\name(f, n)}
\Params{
{\em f} & $\QQ(x)$ & The function to differentiate\\
{\em n} & $\ZZ$ & The order of differentiation (optional)\\
}
\Retval{
\name~f returns $f'$, the derivative of $f$.\\
\name(f, n) returns $f^{(n)}$, the \Th{n} derivative of $f$.
}
\alseealso{\alexp{apply}}
#endif
		dualFirstIntegral: (%, %) -> Partial %;
#if ALDOC
\alpage{dualFirstIntegral}
\Usage{\name(L, n)}
\Params{
{\em L} & $\weyl$ & A differential operator\\
{\em n} & $\ZZ$ & A positive integer\\
}
\Retval{
Returns a matrix whose columns form a basis for the space of solutions of
$$
Y' = Sym(A,n) Y
$$
where $A$ is the companion matrix of $L$ and $Sym(A,n)$ is the matrix
of the $\sth{n}$ symmetric power of $Y' = A Y$.
}
\begin{alex}
We compute a basis for the dual first integrals of degree $4$ of
$$
L = \frac{d^3}{dx^3} +{{7\,x-4} \over {x^{2}-x}}\,\frac{d^2}{dx^2}+
{{{{72} \over {7}}\,x^{2}-{{2963} \over {252}}\,x+{{20} \over {9}}}
\over {x^{4}-2\,x^{3}+x^{2}}}\,\frac{d}{dx} +{{{{792} \over {343}}\,x
-{{40805} \over {24696}}} \over {x^{4}-2\,x^{3}+x^{2}}}
$$
\begin{ttyout}
1 --> L := D^3 + (7*x-4)/(x*(x-1)) * D^2
     + (2592*x^2 - 2963*x + 560)/(252*x^2*(x-1)^2) * D
     + (57024*x - 40805) / (24696*x^2*(x-1)^2);
2 --> C := dualFirstIntegral(L,4);
3 --> tex(C);
\end{ttyout}
$$
\pmatrix{
0 \cr 
0 \cr 
-{{1372257936} \over {x^{7}-3\,x^{6}+3\,x^{5}-x^{4}}} \cr 
{{457419312} \over {x^{7}-3\,x^{6}+3\,x^{5}-x^{4}}} \cr 
0 \cr 
-{{1344252672\,x^{2}-1534844052\,x+1219784832} \over
{x^{11}-5\,x^{10}+10\,x^{9}-10\,x^{8}+5\,x^{7}-x^{6}}} \cr 
-{{1600967592\,x-914838624} \over {x^{9}-4\,x^{8}+6\,x^{7}-4\,x^{6}+x^{5}}} \cr 
{{3024568512\,x^{2}-3456575640\,x+1118136096} \over
{x^{11}-5\,x^{10}+10\,x^{9}-10\,x^{8}+5\,x^{7}-x^{6}}} \cr 
-{{6529227264\,x^{3} -11194159662\,x^{2}+6399313956\,x-1219784832} \over
{x^{13}-6\,x^{12}+15\,x^{11}-20\,x^{10}+15\,x^{9}-6\,x^{8}+x^{7}}} \cr 
{{16131032064\,x^{3}-20748483315\,x^{2}+9731458800\,x-1016487360} \over
{x^{14}-6\,x^{13}+15\,x^{12}-20\,x^{11}+15\,x^{10}-6\,x^{9}+x^{8}}} \cr 
{{3734035200\,x^{2}-4267691064\,x+1219784832} \over
{x^{11}-5\,x^{10}+10\,x^{9}-10\,x^{8}+5\,x^{7}-x^{6}}} \cr 
-{{8401579200\,x^{3}-14403262860\,x^{2}+8689022118\,x-1829677248} \over
{x^{13}-6\,x^{12}+15\,x^{11}-20\,x^{10}+15\,x^{9}-6\,x^{8}+x^{7}}} \cr 
{{19971753984\,x^{4}-45653164515\,x^{3}+40867528359\,x^{2}
-16890145944\,x+2733221568} \over {x^{15}-7\,x^{14}+21\,x^{13}
-35\,x^{12}+35\,x^{11}-21\,x^{10}+7\,x^{9}-x^{8}}} \cr 
-{{49474768896\,x^{5}
-141373731429\,x^{4}+167210189622\,x^{3}-{{203967305199} \over
{2}}\,x^{2}+31896217584\,x-4065949440} \over
{x^{17}-8\,x^{16}+28\,x^{15}-56\,x^{14}
+70\,x^{13}-56\,x^{12}+28\,x^{11}-8\,x^{10}+x^{9}}} \cr 
{{125769646080\,x^{6}-431281578816\,x^{5}+{{1269498305493} \over
{2}}\,x^{4}-511939410245\,x^{3}+236953524228\,x^{2}-59117120160\,x
+6023628800} \over {x^{19}-9\,x^{18}+36\,x^{17}-84\,x^{16}
+126\,x^{15}-126\,x^{14}+84\,x^{13}-36\,x^{12}+9\,x^{11}-x^{10}}}\cr } 
$$
\end{alex}
% \alseealso{\alexp{invariants}, \alexp{symmetricKernel}}
\alseealso{\alexp{symmetricKernel}}
#endif
		eigenring: % -> Partial %;
		eigenring: (%, %) -> Partial %;
#if ALDOC
\alpage{eigenring}
\Usage{\name~L\\ \name~A}
\Params{
{\em L} & $\weyl$ & A differential operator\\
{\em A} & $\QQ(x)^{n,n}$ & A matrix of fractions\\
}
\Descr{
\name(L) returns a basis $R_1,\dots,R_m$ of the eigenring of \emph{L},
\ie the set of operators $R\in \weylq$ of order strictly less than
the order of \emph{L} and such that $L R = S L$ for some operator \emph{S}.\\
\name(A) returns an $n$ by $nm$ matrix $M = [B_1|\dots|B_m]$
such that $B_1,\dots,B_m$ for a basis of the eigenring of $Y' = A Y$,
\ie~the set of matrices $B\in \QQ(x)^{n,n}$ such that $B' = A B - B A$.}
\begin{alex}
We compute the eigenring of the differential system
\begin{equation}
\label{eq:exeigen}
Y' =
\left [\begin {array}{ccc} {x}^{3}&{\frac {{x}^{5}+{x}^{2}-3+{x}^{4}}{
{x}^{2}}}&{\frac {-3+{x}^{4}+3\,x}{{x}^{2}}}\\\noalign{\medskip}-{x}^{
3}&-{\frac {{x}^{5}-3+{x}^{4}}{{x}^{2}}}&-{\frac {-{x}^{2}-3+{x}^{4}+3
\,x}{{x}^{2}}}\\\noalign{\medskip}{x}^{3}&{\frac {{x}^{5}-3+{x}^{4}}{{
x}^{2}}}&{\frac {-3+{x}^{4}+3\,x}{{x}^{2}}}\end {array}\right ] Y
\end{equation}
as follows:
\begin{ttyout}
1 --> A := system(x^3,(x^5+x^2-3+x^4)/x^2,(-3+x^4+3*x)/x^2,
                 -x^3,-(x^5-3+x^4)/x^2,-(-x^2-3+x^4+3*x)/x^2,
                  x^3,(x^5-3+x^4)/x^2,(-3+x^4+3*x)/x^2);
2 --> e := eigenring(A);
3 --> tex(e);
\end{ttyout}
$$
\pmatrix{
1 & 0 & 0 & x^{2}+2\,x+1 & {{x^{5}+x^{4}+x^{2}+x+1} \over {x^{3}}} & {{-x^{4}+1} \over {x^{3}}} & x^{2}+x & {{x^{4}+x^{3}+x+1} \over {x^{2}}} & {{1} \over {x^{2}}} \cr 
0 & 1 & 0 & -x^{2}-2\,x+2 & {{-x^{5}-x^{4}+3\,x^{3}-x+1} \over {x^{3}}} & {{x^{4}+x^{2}-2\,x+1} \over {x^{3}}} & -x^{2}-x+1 & {{-x^{5}-x^{4}+x^{3}-x+1} \over {x^{3}}} & {{x^{2}-2\,x+1} \over {x^{3}}} \cr 
0 & 0 & 1 & x^{2}-2 & {{x^{5}-x^{4}-2\,x^{3}-1} \over {x^{3}}} & {{-x^{4}+x^{3}+x-1} \over {x^{3}}} & x^{2}-1 & {{x^{5}-x^{3}-1} \over {x^{3}}} & {{x-1} \over {x^{3}}}\cr } 
$$
This means that a basis of the eigenring of~(\ref{eq:exeigen}) is
$$
\pmatrix{
1 & 0 & 0 \cr
0 & 1 & 0 \cr
0 & 0 & 1 \cr },
\quad
\pmatrix{
x^{2}+2\,x+1 & {{x^{5}+x^{4}+x^{2}+x+1} \over {x^{3}}} & {{-x^{4}+1} \over {x^{3}}} \cr
-x^{2}-2\,x+2 & {{-x^{5}-x^{4}+3\,x^{3}-x+1} \over {x^{3}}} & {{x^{4}+x^{2}-2\,x+1} \over {x^{3}}} \cr
x^{2}-2 & {{x^{5}-x^{4}-2\,x^{3}-1} \over {x^{3}}} & {{-x^{4}+x^{3}+x-1} \over {x^{3}}} \cr },
$$
$$
\mbox{and }
\pmatrix{
x^{2}+x & {{x^{4}+x^{3}+x+1} \over {x^{2}}} & {{1} \over {x^{2}}} \cr 
-x^{2}-x+1 & {{-x^{5}-x^{4}+x^{3}-x+1} \over {x^{3}}} & {{x^{2}-2\,x+1} \over {x^{3}}} \cr 
x^{2}-1 & {{x^{5}-x^{3}-1} \over {x^{3}}} & {{x-1} \over {x^{3}}}\cr } 
$$
\end{alex}
\begin{maplerem}
When using \name(A,D,x) from inside \maple, the matrix $[B_1|\dots|B_m]$
returned from \bernina{} is transformed into the array of matrices
$[B_1,\dots,B_m]$.
So the above example in \maple{} would be:
\begin{ttyout}
> A := matrix(3, 3, [x^3,(x^5+x^2-3+x^4)/x^2,(-3+x^4+3*x)/x^2,
                    -x^3,-(x^5-3+x^4)/x^2,-(-x^2-3+x^4+3*x)/x^2,
                     x^3,(x^5-3+x^4)/x^2,(-3+x^4+3*x)/x^2]);
> eigenring(A, D, x);
\end{ttyout}
$$
\left[ \pmatrix{
1 & 0 & 0 \cr
0 & 1 & 0 \cr
0 & 0 & 1 \cr },
\quad
\pmatrix{
x^{2}+2\,x+1 & {{x^{5}+x^{4}+x^{2}+x+1} \over {x^{3}}} & {{-x^{4}+1} \over {x^{3}}} \cr
-x^{2}-2\,x+2 & {{-x^{5}-x^{4}+3\,x^{3}-x+1} \over {x^{3}}} & {{x^{4}+x^{2}-2\,x+1} \over {x^{3}}} \cr
x^{2}-2 & {{x^{5}-x^{4}-2\,x^{3}-1} \over {x^{3}}} & {{-x^{4}+x^{3}+x-1} \over {x^{3}}} \cr },
\right.
$$
$$
\left.
\pmatrix{
x^{2}+x & {{x^{4}+x^{3}+x+1} \over {x^{2}}} & {{1} \over {x^{2}}} \cr 
-x^{2}-x+1 & {{-x^{5}-x^{4}+x^{3}-x+1} \over {x^{3}}} & {{x^{2}-2\,x+1} \over {x^{3}}} \cr 
x^{2}-1 & {{x^{5}-x^{3}-1} \over {x^{3}}} & {{x-1} \over {x^{3}}}\cr } 
\right]
$$
\end{maplerem}
#endif
		element: (%, %) -> Partial %;
#if ALDOC
\alpage{element}
\Usage{\name(v, k)}
\Params{
{\em v} & $\QQ(x)^n$ & A vector of functions\\
{\em k} & $\ZZ$ & A positive index\\
}
\Retval{Returns the \Th{k} element of $v$, the first element having index $1$.}
#endif
		exponentialSolutions: % -> Partial %;
#if ALDOC
\alpage{exponentialSolutions}
\Usage{\name~L}
\Params{ {\em L} & $\weyl$ & A differential operator\\ }
\Retval{Returns $[p_1(x,u),\dots,p_n(x,u)]$ such that the
exponential solutions of \emph{L} are described by
$$
\bigcup_{i=1}^n
\left\{ \paren{\sum_{j=1}^{m_i} c_j f_{ij}(x)} e^{\int f_{i0}(x) dx} \right\}
$$
where $p_i(x,u) = \sum_{j=0}^{m_i} f_{ij}(x) u^j$
and the $c_j$ are arbitrary constants.}
\Remarks{\name~returns only the solutions that are exponential
over $\QQ(x)$, \ie~the solutions $y$ such that $y'/y \in \QQ(x)$.
It does not return any eventual solution that is exponential over
$\overline{\QQ}(x)$ but not over $\QQ(x)$.}
\begin{alex}
We compute the exponential solutions of
\begin{equation}
\label{eq:exexpsol}
\frac{d^3 y}{dx^3} - \frac{x^3+1}x \frac{d^2 y}{dx^2}
+ (2x^2-3x) \frac{dy}{dx} + 2 x^4 y = 0
\end{equation}
as follows:
\begin{ttyout}
1 --> L := D^3-(1+x^3)/x*D^2+(-3*x-2*x^2)*D+2*x^4;
2 --> e := exponentialSolutions(L);
3 --> tex(e);
\end{ttyout}
$$
[ u+x^{2} ]
$$
This means that the exponential solutions of~(\ref{eq:exexpsol})
form a one-dimensional vector space generated by $e^{\int x^2 dx}$.
\end{alex}
\begin{maplerem}
When using \name{} from inside \maple, the result
returned from \bernina{} is transformed into actual exponentials,
so the above example in \maple{} would be:
\begin{ttyout}
> L := D^3-(1+x^3)/x*D^2+(-3*x-2*x^2)*D+2*x^4;
> exponentialSolutions(L, D, x);
\end{ttyout}
$$
\left[{\it \_C}_{{1}}~{e^{\int \!{x}^{2}{dx}}}\right]
$$
\end{maplerem}
\alseealso{\alexp{radicalSolutions}}
#endif
		exteriorKernel: (%, %) -> Partial %;
#if ALDOC
\alpage{exteriorKernel}
\Usage{\name(L, n)}
\Params{
{\em L} & $\weyl$ & A differential operator\\
{\em n} & $\ZZ$ & A positive integer\\
}
\Retval{
% \name~L returns a basis for $\Ker\paren{\extpow{L}{n}} \cap \QQ(x)$,
% where $\extpow{L}{n}$ is the \Th{n} exterior power of $L$.
}
\Remarks{
Using \name~can be more efficient than computing the exterior
power and its exponential solutions separately.
}
% \begin{alex}
% \end{alex}
\alseealso{\alexp{exponentialSolutions},\alexp{exteriorPower}}
#endif
		extPower: (%, %) -> Partial %;
		exteriorPower: (%, %) -> Partial %;
#if ALDOC
\alpage{exteriorPower}
\Usage{\name(L, n)}
\Params{
{\em L} & $\weyl$ & A differential operator\\
{\em n} & $\ZZ$ & A positive integer\\
}
\Retval{
Returns a differential operator $\extpow{L}{n}$
of minimal order whose kernel is generated by the Wronskians of $n$ elements
of a basis of $\Ker(L)$.
}
\begin{alex}
The second exterior power of
$$
L = \frac{d^4}{dx^4} - 2 x \frac{d^2}{dx^2} - 2 \frac d{dx} + x^2
$$
can be computed as follows:
\begin{ttyout}
1 --> L := D^4 - 2*x*D^2 - 2*D + x^2;
2 --> Le2 := exteriorPower(L,2);
3 --> tex(Le2);
\end{ttyout}
$$
D^{5}-4\,x\,D^{3}-6\,D^{2}
$$
\end{alex}
% \alseealso{\alexp{exteriorKernel}, \alexp{symmetricPower}}
\alseealso{\alexp{symmetricPower}}
#endif
		factor: % -> Partial %;
#if ALDOC
\alpage{factor}
\altarget{dfactor}
\Usage{\name~L}
\Params{ {\em L} & $\weyl$ & A differential operator of order at most 3\\ }
\Descr{Returns one of the following possible results:
\begin{itemize}
\item[(i)] \emph{L}, in which case \emph{L} is irreducible
in ${\overline \QQ}(x)[d/dx]$.
\item[(ii)] $[m,L_1,\dots,L_n]$ where $m \ge 0$ and $L_i \in \weylq$,
in which case each $L_i$ is irreducible in ${\overline \QQ}(x)[d/dx]$,
and \emph{L} can be expressed in terms of the $L_i$'s depending on $m$
as in the following table: 
\begin{center}
\begin{tabular}{c|l}
\emph{m} & \emph{L}\\
\hline
0 & LeftLcm($L_1,\dots,L_n$)\\
1 & $L_1 \cdots L_n$\\
2 & LeftLcm($L_1, L_2 L_3$)\\
3 & $L_1$ LeftLcm($L_2, L_3$)\\
4 & $L_1$ LeftLcm($L_2, L_3$) $L_4$\\
\end{tabular}
\end{center}
\item[(iii)] $[m,h(x),a(x,u),b(x,u),f_1(x,u),\dots,f_n(x,u)]$,
where $m < 0$, $h(x) \in \QQ[x]$ is irreducible and $a(x,u)$,
$b(x,u)$, $f_1(x,u),\dots,f_n(x,u) \in \QQ(x)[u]$,
in which case each $f_i(x,D)$ is irreducible in ${\overline \QQ}(x)[d/dx]$,
and \emph{L} can be expressed depending on $m$ as in the following table:
\begin{center}
\begin{tabular}{c|l}
\emph{m} & \emph{L}\\
\hline
-1 & LeftLcm($D + a(\alpha, x)/b(\alpha, x), f_1(x,D),\dots,f_n(x,D)$)\\
-4 & $f_1(x,D)$ LeftLcm($D + a(\alpha, x)/b(\alpha, x)$)\\
-5 & $f_1(x,D)$ LeftLcm($D + a(\alpha, x)/b(\alpha, x)$) $f_2(x,D)$\\
\end{tabular}
\end{center}
where $\alpha$ ranges over all the roots of $h(x)$.
\end{itemize}
}
\begin{alex}
We factor the differential equation
\begin{equation}
\label{eq:exfactor}
\frac{d^3 y}{dx^3} - x \frac{d^2 y}{dx^2} -
(x^2-1) \frac{dy}{dx} + (x^3-3x) y = 0
\end{equation}
as follows:
\begin{ttyout}
1 --> L := D^3-x*D^2+(-x^2+1)*D-3*x+x^3;
2 --> v := factor(L);
3 --> tex(v);
\end{ttyout}
$$
\left[ 2 , D-x , D-x , D+x \right]
$$
This means that the operator of~(\ref{eq:exfactor}) is a least
common left multiple of $d/dx - x$ and of the product
$(d/dx - x)(d/dx + x)$, which itself is not a least common left
multiple of irreducible operators.
\end{alex}
\begin{maplerem}
In order not to conflict with the {\tt factor}
function in \maple, \name~is available under \maple{} under the name
{\tt dfactor}.
In addition, when using {\tt dfactor} from inside \maple,
the result returned from
\bernina{} is further transformed as in the case of
the \alexp{decompose} function.
So the above example in \maple{} would be:
\begin{ttyout}
> L := D^3-x*D^2+(-x^2+1)*D-3*x+x^3;
> dfactor(L, D, x);
\end{ttyout}
$$
{\it LeftLcm}(D-x,\left[D-x,D+x\right])
$$
\end{maplerem}
\alseealso{\alexp{decompose},\alexp{Loewy}}
#endif
		invariants: (%, %) -> Partial %;
		radicalInvariants: (%, %) -> Partial %;
		radicalInvariants: (%, %, %) -> Partial %;
		semiInvariants: (%, %) -> Partial %;
#if ALDOC
\alpage{invariants}
\Usage{\name(L, n)}
\Params{
{\em L} & $\weyl$ & A differential operator\\
{\em n} & $\ZZ$ & A positive integer\\
}
\Retval{Returns a basis for the homogeneous invariants of degree $n$ of
the Galois group of $L$. The basis is returned as a matrix where each column
is an invariant encoded on $N+3$ rows as follows:
the first $N$ entries are the coefficients of the invariant in the
lexicographic basis $\{X_1^n,X_1^{n-1}X_2,\dots,X_d^n\}$ where $d$ is the
degree of $L$ in $d/dx$, while the entry at row $N+1$ is the value $a$ of the
invariant, the entry at row $N+2$ is always 0,
and the last entry is $p \in \QQ(x)[u]$
such that $p/a$ would be a Riccati polynomial if the invariant factors
linearly.}
\begin{alex}
We compute a basis for the homogeneous invariants of degree $4$ of
$$
L = \frac{d^3}{dx^3} +{{7\,x-4} \over {x^{2}-x}}\,\frac{d^2}{dx^2}+
{{{{72} \over {7}}\,x^{2}-{{2963} \over {252}}\,x+{{20} \over {9}}}
\over {x^{4}-2\,x^{3}+x^{2}}}\,\frac{d}{dx} +{{{{792} \over {343}}\,x
-{{40805} \over {24696}}} \over {x^{4}-2\,x^{3}+x^{2}}}
$$
\begin{ttyout}
1 --> L := D^3 + (7*x-4)/(x*(x-1)) * D^2
     + (2592*x^2 - 2963*x + 560)/(252*x^2*(x-1)^2) * D
     + (57024*x - 40805) / (24696*x^2*(x-1)^2);
2 --> I := invariants(L,4);
3 --> tex(I);
\end{ttyout}
$$
\pmatrix{
0 \cr 
0 \cr 
702596063232 \cr 
-351298031616 \cr 
0 \cr 
786985258752 \cr 
-644046391296 \cr 
-2918123615232 \cr 
-4865757257088 \cr 
-3048157538496 \cr 
-295088355072 \cr 
-2132706651264 \cr 
-6053559089760 \cr 
-7936072153128 \cr 
-4011668122151 \cr 
0\cr
{{2810384252928} \over {x^{7}-3x^{6}+3x^{5}-x^{4}}} u^{2}+
{{6557563256832x-3747179003904} \over {x^{9}-4\,x^{8}+6\,x^{7}-4x^{6}+x^{5}}}u
+{{3823652044800x^{2}-4370115649536x+1249059667968}
\over {x^{11}-5x^{10}+10x^{9}-10x^{8}+5x^{7}-x^{6}}}\cr } 
$$
Since the lexicographic basis is
$\{X_1^4,X_1^3 X_2,X_1^3 X_3, \dots, X_3^4\}$, the above means that
there is a one-dimensional space of homogeneous invariants of degree $4$
generated by
\begin{eqnarray*}
&& 702596063232 X_1^3 X_3 -351298031616 X_1^2 X_2^2 + 786985258752 X_1^2 X_3^2
-644046391296 X_1 X_2^3\\
&&  -2918123615232 X_1 X_2^2 X_3
-4865757257088 X_1 X_2 X_3^2 -3048157538496 X_1 X_3^3 -295088355072 X_2^4\\
&& -2132706651264 X_2^3 X_3 -6053559089760 X_2^2 X_3^2 -7936072153128 X_2 X_3^3
-4011668122151 X_3^4
\end{eqnarray*}
whose value is $0$, and whose corresponding candidate Riccati polynomial is
\begin{eqnarray*}
{{2810384252928} \over {x^{7}-3x^{6}+3x^{5}-x^{4}}} u^{2}&+&
{{6557563256832x-3747179003904} \over {x^{9}-4\,x^{8}+6\,x^{7}-4x^{6}+x^{5}}}u\\
&+&{{3823652044800x^{2}-4370115649536x+1249059667968}
\over {x^{11}-5x^{10}+10x^{9}-10x^{8}+5x^{7}-x^{6}}}\,.
\end{eqnarray*}
Since the value is $0$, it follows that the invariant does not factor
linearly and the the above polynomial is in fact not a Riccati polynomial.
\end{alex}
\begin{maplerem}
When using \name~from inside \maple, you must give the symbol for the
returned candidate Riccati polynomials as an extra argument.
In addition, the output is modified within \maple in order to
return a list of pairs of the form $[I(X_1,\dots,X_n)=a, p(x,u)]$
where $I$ is the actual polynomial invariant, and $a$ and $p$ are
as explained earlier. So the above example in \maple would be:
\begin{ttyout}
> L := D^3 + (7*x-4)/(x*(x-1)) * D^2
     + (2592*x^2 - 2963*x + 560)/(252*x^2*(x-1)^2) * D
     + (57024*x - 40805) / (24696*x^2*(x-1)^2);
> invariants(L,4,D,x,u);
\end{ttyout}
\begin{eqnarray*}
&&\left[\left[
702596063232 X_1^3 X_3 -351298031616 X_1^2 X_2^2 + 786985258752 X_1^2 X_3^2
-644046391296 X_1 X_2^3 \right.\right. \\
&&-2918123615232 X_1 X_2^2 X_3
-4865757257088 X_1 X_2 X_3^2 -3048157538496 X_1 X_3^3 -295088355072 X_2^4 \\
&&-2132706651264 X_2^3 X_3 -6053559089760 X_2^2 X_3^2 -7936072153128 X_2 X_3^3
-4011668122151 X_3^4 = 0,\\
&&{{2810384252928} \over {x^{7}-3x^{6}+3x^{5}-x^{4}}} u^{2}+
{{6557563256832x-3747179003904} \over
{x^{9}-4\,x^{8}+6\,x^{7}-4x^{6}+x^{5}}}u \\
&&\left.\left. +{{3823652044800x^{2}-4370115649536x+1249059667968}
\over {x^{11}-5x^{10}+10x^{9}-10x^{8}+5x^{7}-x^{6}}}\right]\right]
\end{eqnarray*}
\end{maplerem}
% \alseealso{\alexp{dualFirstIntegral}}
#endif
		irreducible3: (%, %) -> Partial %;
		kernel: % -> Partial %;
		kernel: (%, %) -> Partial %;
		-- second argument = denoms, last argument = degree bound
--		kernel: (%, List %, %) -> Partial %; LATER
#if ALDOC
\alpage{kernel}
\altarget{polynomialKernel}
\altarget{rationalKernel}
\Usage{\name~L \\ \name(L, p) \\ \name~A} % \\ \name(A, p)}
\Params{
{\em L} & $\weyl$ & A differential operator\\
{\em A} & $\QQ(x)^{n,n}$ & A matrix of fractions\\
{\em p} & $\QQ[x]$ & A polynomial\\
}
\Descr{\name~L returns a basis for $\Ker~L \cap \QQ(x)$, while
\name~A returns a basis for $\Ker(Y' = A Y) \cap \QQ(x)^n$.
% In both cases, if
If
a second argument $p$ is present, then a basis for the
subspace of all solutions whose denominator $b \in \QQ[x]$
has all its roots among the roots of $p$.
For example, \name(L, 1) returns a basis for $\Ker~L \cap \QQ[x]$,
the space of all the polynomial solutions of $L y = 0$.}
\begin{alex}
The operator
$$
L =
\frac{d^3}{dx^3}+{{5\,x^{4}-{{8} \over {15}}\,x^{2}-{{1} \over {5}}}
\over {x^{5}-{{14} \over {15}}\,x^{3}-{{1} \over {15}}\,x}}\,\frac{d^2}{dx}+
{{-26\,x^{2}-{{22} \over {15}}} \over {x^{4}-{{14}
\over {15}}\,x^{2}-{{1} \over {15}}}}\,\frac{d}{dx}+{{-30\,x^{2}-6}
\over {x^{5}-{{14} \over {15}}\,x^{3}-{{1} \over {15}}\,x}}
$$
has the following rational kernel:
\begin{ttyout}
1 --> L := D^3+(5*x^4-8/15*x^2-1/5)/(x^5-14/15*x^3-1/15*x)*D^2
              +(-26*x^2-22/15)/(x^4-14/15 *x^2-1/15)*D
              +(-30*x^2-6)/(x^5-14/15*x^3-1/15*x);
2 --> K := kernel(L);
3 --> tex(K);
\end{ttyout}
$$
[{{1} \over {x}}, x^{5}-{{10} \over {9}}\,x^{3}+{{5} \over {21}}\,x]
$$
To compute its polynomial kernel:
\begin{ttyout}
4 --> P := kernel(L, 1);
5 --> tex(P);
\end{ttyout}
$$
[ x^{5}-{{10} \over {9}}\,x^{3}+{{5} \over {21}}\,x ]
$$
Finally for the elements of the kernel whose denominator is a power of $x$
(although the result is the same as the rational kernel above, this
computation is about 3 times faster):
\begin{ttyout}
6 --> K1 := kernel(L, x);
7 --> tex(K1);
\end{ttyout}
$$
[{{1} \over {x}}, x^{5}-{{10} \over {9}}\,x^{3}+{{5} \over {21}}\,x]
$$
\end{alex}
\begin{maplerem}
In order not to conflict with the {\tt linalg[kernel]}
function in \maple, \name~is available under \maple under the names
{\tt polynomialKernel} and {\tt rationalKernel}.
So the above examples in \maple{} would be:
\begin{ttyout}
> L := D^3+(5*x^4-8/15*x^2-1/5)/(x^5-14/15*x^3-1/15*x)*D^2
              +(-26*x^2-22/15)/(x^4-14/15 *x^2-1/15)*D
              +(-30*x^2-6)/(x^5-14/15*x^3-1/15*x);
> rationalKernel(L,D,x);
\end{ttyout}
$$
\left[{{1} \over {x}}, x^{5}-{{10} \over {9}}\,x^{3}+{{5} \over {21}}\,x\right]
$$
\begin{ttyout}
> polynomialKernel(L,D,x);
\end{ttyout}
$$
\left[ x^{5}-{{10} \over {9}}\,x^{3}+{{5} \over {21}}\,x \right]
$$
\end{maplerem}
% \alseealso{\alexp{parametricKernel}, \alexp{polynomialSolution},
\alseealso{\alexp{polynomialSolution},
\alexp{rationalSolution}}
#endif
		leftGcd: (%, %) -> Partial %;
#if ALDOC
\alpage{leftGcd}
\Usage{\name(A, B)\\ \name(p, q)}
\Params{
{\em A, B} & $\weyl$ & Differential operators\\
{\em p, q} & $\QQ[x]$ & Polynomials\\
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
{\em A, B} & $\weyl$ & Differential operators\\
{\em p, q} & $\QQ[x]$ & Polynomials\\
}
\Retval{
\name(A, B) returns $L$ such that $L = S A = T B$, and every other
left multiple of $A$ and $B$ is a left multiple of $L$, while
\name(p, q) returns $\lcm(p, q)$.
}
\begin{alex}
An annihilator of $\log(x) + \log(x+1)$ can be obtained by computing the
least common left multiple of the annihilators $L_1 = x d/dx + 1$ and
$L_2 = (x + 1) d^2/dx^2 + d/dx$ of $\log(x)$ and $\log(x+1)$ respectively:
\begin{ttyout}
1 --> L1 := x*D^2 + D;
2 --> L2 := (x+1)*D^2 + D;
3 --> L := leftLcm(L1, L2);
4 --> tex(L);
\end{ttyout}
$$
D^{3}+{{4\,x+2} \over {x^{2}+x}}\,D^{2}+{{2} \over {x^{2}+x}}\,D
$$
\end{alex}
\alseealso{\alexp{leftGcd}, \alexp{rightGcd}, \alexp{rightLcm}}
#endif
		-- list: List % -> Partial %;
		Loewy: % -> Partial %;
#if ALDOC
\alpage{Loewy}
\Usage{\name~L}
\Params{ {\em L} & $\weyl$ & A differential operator of order at most 3\\ }
\Retval{Returns either \emph{L}, in which case \emph{L} is completely
reducible, or a right Loewy decomposition $[L_1,\dots,L_n]$
where $L = L_1 \cdots L_n$ and each $L_i \in \weylq$ is a completely reducible
right-factor of maximal order of $L_1 \cdots L_{i-1}$.
}
\begin{alex}
We compute the Loewy decomposition of the differential equation
\begin{equation}
\label{eq:exloewy}
\frac{d^3 y}{dx^3} - \frac{x^2+1}x \frac{d^2 y}{dx^2} -
\frac{2x^4-x^2-1}{x^2} \frac{dy}{dx} + (2x^3-4x) y = 0
\end{equation}
as follows:
\begin{ttyout}
1 --> L := D^3-(x^2+1)/x*D^2-(-x^2-1+2*x^4)/x^2*D+2*x^3-4*x;
2 --> v := Loewy(L);
3 --> tex(v);
\end{ttyout}
$$
\left[ D-x, D^{2}-{{1} \over {x}}\,D-2\,x^{2} \right]
$$
This means that the operator of~(\ref{eq:exloewy}) factors as
$$
\paren{\frac d{dx} - x}\paren{\frac{d^2}{dx^2} - \frac 1x \frac d{dx} - 2x^2}
$$
where the second-order factor is a completely reducible right-factor
of maximal order. Note that is is reducible in this example:
\begin{ttyout}
4 --> w := decompose(element(v,2));
5 --> tex(w);
\end{ttyout}
$$
\left[ x^{2}-2 , x\,u , 1 \right]
$$
which means that
$$
\frac{d^2}{dx^2} - \frac 1x \frac d{dx} - 2x^2
$$
is a least common left multiple of $d/dx - x \sqrt{2}$ and
$d/dx + x \sqrt{2}$.
\end{alex}
\alseealso{\alexp{decompose},\alexp{factor}}
#endif
		makeIntegral: % -> Partial %;
#if ALDOC
\alpage{makeIntegral}
\Usage{\name~L\\ \name~w}
\Params{
{\em L} & $\weyl$ & A differential operator\\
{\em w} & $(\QQ(x)[u])^n$ & A vector of Darboux curves\\
}
\Retval{
\name~L returns the primitive multiple of $L$ in $\weyl$,
while \name~w returns the vector of primitive multiples of the $w_i$'s
in $\QQ[x,y]$.
}
\begin{alex}
\begin{ttyout}
1 --> L := D^2 + 3/16/x^2;
2 --> tex(makeIntegral(L));
\end{ttyout}
$$
x^{2}\,D^{2}+{{3} \over {16}}
$$
\begin{ttyout}
3 --> w := Darboux(L);
4 --> tex(w);
\end{ttyout}
$$
[ u^{2}-{{1} \over {x}}\,u+{{{{3} \over {16}}} \over {x^{2}}} ]
$$
\begin{ttyout}
5 --> tex(makeIntegral(w));
\end{ttyout}
$$
[ x^{2}\,u^{2}-x\,u+{{3} \over {16}} ]
$$
\end{alex}
\alseealso{\alexp{normalize}}
#endif
		normalize: % -> Partial %;
#if ALDOC
\alpage{normalize}
\Usage{\name~L \\ \name~p \\ \name~q}
\Params{
{\em L} & $\weyl$ & A differential operator\\
{\em p} & $\QQ[x]$ & A polynomial\\
{\em q} & $\QQ(x)[u]$ & A Darboux curve\\
}
\Descr{\name~makes its argument monic in the outermost variable.}
\Remarks{\name~can also be used on vectors and quotients of polynomials.}
\begin{alex}
\begin{ttyout}
1 --> L := x^2*D^2 + 3/16 - x;
2 --> tex(normalize(L));
\end{ttyout}
$$
D^{2}+{{-x+{{3} \over {16}}} \over {x^{2}}}
$$
\begin{ttyout}
3 --> f := (2*x + 1)/(3*x^2 - 1);
4 --> tex(normalize(f));
\end{ttyout}
$$
{{x+{{1} \over {2}}} \over {x^{2}-{{1} \over {3}}}}
$$
\end{alex}
\alseealso{\alexp{makeIntegral}}
#endif
--		parametricKernel: (%, List %) -> Partial %; LATER
#if LATER_ALDOC
\alpage{parametricKernel}
\Usage{\name(L, $g_1,\dots,g_m$)}
\Params{
{\em L} & $\weyl$ & A differential operator\\
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
\left[ [x],
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
		pCurvature: (%, %) -> Partial %;
#if ALDOC
\alpage{pCurvature}
\Usage{\name(L, p)\\ \name(A, p)}
\Params{
{\em L} & $\weyl$ & A differential operator\\
{\em A} & $\QQ(x)^{n,n}$ & A matrix of fractions\\
{\em p} & $\ZZ$ & A prime\\
}
\Descr{\name($L,p$) returns the p-curvature of \emph{L}, \ie the right-remainder
of $d^p/dx^p$ by \emph{L}, while \name($A,p$) returns the
matrix of the p-curvature of the system $d/dx - A$,
\ie~the $F_p(x)$--linear map $(d/dx - A)^p$.}
\Remarks{The rational numbers appearing in \emph{L} or \emph{A}
must be reducible modulo \emph{p}.}
% \begin{alex}
% The $11$-curvature of the Airy operator
% $$
% \frac{d^2}{dx^2} - x
% $$
% can be computed in the following way:
% \begin{ttyout}
% 1 --> L := D^2-x;
% 2 --> M := pCurvature(L,11);
% 3 --> tex(M);
% \end{ttyout}
% $$
% \pmatrix{
% 8\,x^{4}+6\,x & 10\,x^{5}+5\,x^{2} \cr 
% 10\,x^{6}+4\,x^{3}+6 & 3\,x^{4}+5\,x\cr } 
% $$
% It is possible to conclude from the above matrix that
% $L$ is irreducible in $\FF_{11}(x)[\frac d{dx}]$
% (but reducible in $\FF_{11}(\sqrt{x})[\frac d{dx}]$)
% hence that it is irreducible in $\QQ(x)[\frac d{dx}]$.
% \end{alex}
#endif
		polynomialSolution: (%, %) -> Partial %;
#if ALDOC
\alpage{polynomialSolution}
\Usage{\name(L, g)}
\Params{
{\em L} & $\weyl$ & A differential operator\\
{\em g} & $\QQ[x]$ & A polynomial\\
}
\Descr{\name($L,g$) returns either $[p]$ where $p \in \QQ[x]$
satisfies $L p = g$, or $[]$ if $L y = g$ has no solution in $\QQ[x]$.}
\Remarks{\name($L,0$) returns $[0]$ only when $L y = 0$ has no nonzero
polynomial solution.}
\begin{alex}
A particular polynomial solution of
$$
x^3 \frac{d^3y}{dx^3}+x^2 \frac{d^2y}{dx^2}-2x \frac{dy}{dx} +2 y = 2 x^4
$$
can be computed in the following way:
\begin{ttyout}
1 --> L := x^3*D^3+x^2*D^2-2*x*D+2;
2 --> p := polynomialSolution(L,2*x^4);
3 --> tex(p);
\end{ttyout}
$$
[ {{1} \over {15}}\,x^{4} ]
$$
\end{alex}
\begin{maplerem}
When using \name~from inside \maple, the output is modified and
either a polynomial solution in $p \in \QQ[x]$ or $[]$ is returned.
So the above example in \maple would be:
\begin{ttyout}
> L := x^3*D^3+x^2*D^2-2*x*D+2;
> polynomialSolution(L,2*x^4,D,x);
\end{ttyout}
$$
{{1} \over {15}}\,x^{4}
$$
\end{maplerem}
% \alseealso{\alexp{kernel}, \alexp{parametricKernel}, \alexp{rationalSolution}}
\alseealso{\alexp{kernel}, \alexp{rationalSolution}}
#endif
		radicalSolutions: (%, %) -> Partial %;
#if ALDOC
\alpage{radicalSolutions}
\Usage{\name~L\\ \name(L,m)}
\Params{
{\em L} & $\weyl$ & A differential operator\\
\emph{m} & $\ZZ$ & A positive integer\\
}
\Retval{Returns a matrix
$$
\pmatrix{
p_1(x,u) & f_{11}(x) & \cdots & f_{1n}(x) \cr
p_2(x,u) & f_{21}(x) & \cdots & f_{2n}(x) \cr
\vdots & \vdots & \cdots & \vdots \cr
p_s(x,u) & f_{s1}(x) & \cdots & f_{sn}(x) \cr }
$$
such that the radical solutions of \emph{L} are described by
$$
\bigcup_{i=1}^s
\left\{ \paren{\sum_{j=1}^n c_j f_{ij}(x)}
\prod_{j=0}^{(n_j-1)/2} p_{i,2j+1}(x)^{p_{i,2j}}
\right\}
$$
where $p_i(x,u) = \sum_{j=0}^{n_j} p_{ij}(x) u^j$
and the $c_j$ are arbitrary constants.
If a second argument $m > 0$ is present, then only the solutions $y$
such that $y^m \in \QQ(x)$ are returned.}
\Remarks{\name~returns only the solutions that are radical
over $\QQ$, \ie~the solutions $y$ such that $y^e \in \QQ(x)$
for some integer $e > 0$.
It does not return any eventual solution that is radical over
$\overline{\QQ}$ but not over $\QQ$.}
\begin{alex}
We compute the radical solutions of
\begin{equation}
\label{eq:exradsol}
16 \frac {d^2 y}{dx^2} + \frac{3}{x^2} y = 0
\end{equation}
as follows:
\begin{ttyout}
1 --> L := 16*D^2 + 3/x^2;
2 --> r := radicalSolutions(L);
3 --> tex(r);
\end{ttyout}
$$
\pmatrix{
x\,u+{{1} \over {4}} & 1 \cr 
x\,u+{{3} \over {4}} & 1\cr } 
$$
This means that the radical solutions of~(\ref{eq:exradsol})
form a two-dimensional vector space over the constants generated by
$x^{1/4}$ and $x^{3/4}$.
\end{alex}
\begin{maplerem}
When using \name{} from inside \maple, the result
returned from \bernina{} is transformed into actual radicals,
so the above example in \maple{} would be:
\begin{ttyout}
> L := 16*D^2 + 3/x^2;
> radicalSolutions(L, D, x);
\end{ttyout}
$$
\left[{x}^{3/4},\sqrt [4]{x}\right]
$$
\end{maplerem}
\alseealso{\alexp{exponentialSolutions}}
#endif
		rationalSolution: (%, %) -> Partial %;
#if ALDOC
\alpage{rationalSolution}
\Usage{\name(L, g)}
\Params{
{\em L} & $\weyl$ & A differential operator\\
{\em g} & $\QQ(x)$ & A fraction\\
}
\Descr{\name($L,g$) returns either $[f]$ where $f \in \QQ(x)$
satisfies $L f = g$, or $[]$ if $L y = g$ has no solution in $\QQ(x)$.}
\Remarks{\name($L,0$) returns $[0]$ only when $L y = 0$ has no nonzero
rational solution.}
\begin{maplerem}
When using \name~from inside \maple, the output is modified and
either a rational solution in $f \in \QQ(x)$ or $[]$ is returned.
\end{maplerem}
% \alseealso{\alexp{kernel}, \alexp{parametricKernel}, \alexp{polynomialSolution}}
\alseealso{\alexp{kernel}, \alexp{polynomialSolution}}
#endif
		rightGcd: (%, %) -> Partial %;
#if ALDOC
\alpage{rightGcd}
\Usage{\name(A, B)\\ \name(p, q)}
\Params{
{\em A, B} & $\weyl$ & Differential operator\\
{\em p, q} & $\QQ[x]$ & Polynomials\\
}
\Retval{
\name(A, B) returns $G$ such that $A = S G$, $B = T G$, and every other
exact right divisor of $A$ and $B$ is a right divisor of $G$, while
\name(p, q) returns $\gcd(p, q)$.
}
\begin{alex}
To look for closed-form common solutions of the differential equations
\begin{equation}
\label{eq:exrgcd1}
\frac{d^3 y}{dx^3} - \frac{d^2 y}{dx^2} - x \frac{dy}{dx} + x y = 0
\end{equation}
and
\begin{equation}
\label{eq:exrgcd2}
\frac{d^2 y}{dx^2} + (x - 1) \frac{dy}{dx} - x y = 0
\end{equation}
we look for solutions of their greatest right common divisor as follows:
\begin{ttyout}
1 --> L1 := D^3 - D^2 - x*D + x;
2 --> L2 := D^2 + (x-1)*D - x;
3 --> L := rightGcd(L1, L2);
4 --> tex(L);
\end{ttyout}
$$
D-1
$$
This means that the solutions of
the system~(\ref{eq:exrgcd1})-(\ref{eq:exrgcd2}) are of the
form $y = c e^x$ for any constant $c$.
\end{alex}
\alseealso{\alexp{leftGcd}, \alexp{leftLcm}, \alexp{rightLcm}}
#endif
		rightLcm: (%, %) -> Partial %;
#if ALDOC
\alpage{rightLcm}
\Usage{\name(A, B)\\ \name(p, q)}
\Params{
{\em A, B} & $\weyl$ & Differential operators\\
{\em p, q} & $\QQ[x]$ & Polynomials\\
}
\Retval{
\name(A, B) returns $L$ such that $L = A S = B T$, and every other
right multiple of $A$ and $B$ is a right multiple of $L$, while
\name(p, q) returns $\lcm(p, q)$.
}
\alseealso{\alexp{leftGcd}, \alexp{leftLcm}, \alexp{rightGcd}}
#endif
		solve2: % -> Partial %;
		symmetricKernel: (%, %) -> Partial %;
#if ALDOC
\alpage{symmetricKernel}
\Usage{\name(L, n)}
\Params{
{\em L} & $\weyl$ & A differential operator\\
{\em n} & $\ZZ$ & A positive integer\\
}
\Retval{
\name~L returns a basis for $\Ker\paren{\sympow{L}{n}} \cap \QQ(x)$,
where $\sympow{L}{n}$ is the \Th{n} symmetric power of $L$.
}
\Remarks{
Using \name~can be more efficient than computing the symmetric
power and its kernel separately.
}
\begin{alex}
We compute the rational kernel of the second symmetric power of
$$
L = \frac{d^7}{dx^7} - x \frac d{dx} + \frac 12
$$
as follows:
\begin{ttyout}
1 --> L := D^7 - x*D + 1/2;
2 --> K := symmetricKernel(L, 2);
3 --> tex(K);
\end{ttyout}
$$
[ x ]
$$
\end{alex}
\alseealso{\alexp{kernel}, \alexp{exteriorKernel}, \alexp{symmetricPower}}
#endif
		symPower: (%, %) -> Partial %;
		symmetricPower: (%, %) -> Partial %;
#if ALDOC
\alpage{symmetricPower}
\Usage{\name(L, n)}
\Params{
{\em L} & $\weyl$ & A differential operator\\
{\em n} & $\ZZ$ & A positive integer\\
}
\Retval{
Returns a differential operator $\sympow{L}{n}$
of minimal order whose kernel is generated by the all the products of $n$
elements of a basis of $\Ker(L)$.
}
\Remarks{
If you only want to compute the kernel of $\sympow{L}{n}$ but not
necessarily the symmetric power itself, then use \alexp{symmetricKernel}
instead.
}
\begin{alex}
The kernel of the fourth symmetric power of
$$
L = x^2 \frac{d^2}{dx^2} + \frac 3{16} - x
$$
can be computed as follows:
\begin{ttyout}
1 --> L := x^2*D^2 + 3/16 - x;
2 --> L4 := symmetricPower(L, 4);
3 --> tex(L4);
\end{ttyout}
\begin{eqnarray*}
4\,x^{5}\,D^{5}&+&\left(-80\,x^{4}+15\,x^{3}\right)\,D^{3}+
\left(120\,x^{3}-45\,x^{2}\right)\,D^{2}\\
&+&\left(256\,x^{3}-240\,x^{2}+90\,x\right)\,D+
\left(-256\,x^{2}+240\right)\,x-90
\end{eqnarray*}
\begin{ttyout}
4 --> K := kernel(L4);
5 --> tex(K);
\end{ttyout}
$$
[ x ]
$$
\end{alex}
\alseealso{\alexp{exteriorPower}, \alexp{symmetricKernel}}
#endif
		symmetricSquareRoot: % -> Partial %;
		system: % -> Partial %;
		system: (I, List %) -> Partial %;
#if ALDOC
\alpage{system}
\Usage{\name($a_{11},a_{12},\dots,a_{nn}$)\\ \name(L)}
\Params{
{\em $a_{ij}$} & $\QQ(x)$ & The entries of a square matrix\\
{\em L} & $\weyl$ & A differential operator\\
}
parametricKRetval{\name($a_{11},\dots,a_{nn}$) returns the
system $Y' = A Y$, where $A$ is the square matrix
given by the $a_{ij}$'s, while \name(L) returns the
companion system associated with the operator L.}
\Remarks{The entries of the matrix must be listed by rows.}
\begin{alex}
The system
$$
\left(\begin{array}{c} y_1' \\ y_2' \end{array}\right) =
\left(\begin{array}{cc}
x &  -1/x^2\\
x^2-x^4 & x
\end{array} \right)
\left(\begin{array}{c} y_1 \\ y_2 \end{array}\right)
$$
has the following rational kernel:
\begin{ttyout}
1 --> A := system(x, -1/x^2, x^2-x^4, x);
2 --> K := kernel(A);
3 --> tex(K);
\end{ttyout}
$$
\pmatrix{
{{1} \over {x}} \cr 
x^{2}+1\cr } 
$$
\end{alex}
#endif
} == add {
	Rep == Union(Lodo:QxD, Vec:V QxD, Darb:V QxY, Mat:M QxY);
	import from Rep;

	0:%			== per [0@QxD];
	1:%			== per [1@QxD];
	ident(f:Qx):Qx		== f;
	coerce(n:Z):%		== n::QxD::%;
	coerce(p:QX):%		== { import from Qx; p::Qx::QxD::%; }
	coerce(l:QxD):%		== per [l];
	coerce(A:M QxY):%	== per [A];
	local vec?(a:%):Boolean	== rep(a) case Vec;
	local mat?(a:%):Boolean	== rep(a) case Mat;
	local lodo?(a:%):Boolean== rep(a) case Lodo;
	local darb?(a:%):Boolean== rep(a) case Darb;
	local lodo(a:%):QxD	== rep(a).Lodo;
	local mat(a:%):M QxY	== rep(a).Mat;
	local vec(a:%):V(QxD)	== rep(a).Vec;
	local darb(a:%):V(QxY)	== rep(a).Darb;
	- (a:%):Partial %	== { lodo? a => [(- lodo a)::%]; failed; }
	local Q2Qx(q:Q):Qx	== { import from QX; q::QX::Qx }
	leftLcm(a:%, b:%):Partial %	== lodolcm(a, b, leftLcm);
	rightLcm(a:%, b:%):Partial %	== lodolcm(a, b, rightLcm);
	rightGcd(a:%, b:%):Partial %	== lodogcd(a, b, rightGcd);
	leftGcd(a:%, b:%):Partial %	== lodogcd(a, b, leftGcd);
	local Loewy2(L:ZXD):V QxD	== { import from Q, ORDER2; Loewy L; }
	local Loewy3(L:ZXD):V QxD	== { import from Q, ORDER3; Loewy L; }
	eigenring(a:%, b:%):Partial %	== lodoOrMatModp(a, b, eigenOp, eigenSys);
	pCurvature(a:%, b:%):Partial %	== lodoOrMatModp(a, b, pCurvOp, pCurvSys);
	exteriorPower(a:%, b:%):Partial %	== lodopos(a, b, extpow);
	symmetricPower(a:%, b:%):Partial %	== lodopos(a, b, sympow);
	exteriorKernel(a:%, b:%):Partial %	== lodonpos(a, b, 1$Z, extker);
	radicalSolutions(a:%, b:%):Partial %	== lodonpos(a, b, 0$Z, radsols);
	local lodopmat(f:(QxD, Z) -> SYS Qx)(a:QxD, n:Z):%	== SYS2B(f(a, n))::%;

	allRationalExponents?(a:%):Partial % == {
		import from Q, ZXD, HEQ;
		lodo? a and ~zero?(L := lodo a) => {
			opz := makez makepoly(QXD, QxD, L);
			n:Z := { allRationalExponents?(opz::HEQ) => 1; 0 }
			[n::%];
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
		import from Q, QX, Partial QX, QxD, PZX, RATSOL;
		import from UAF(Z, ZX, Q, QX), UAF(QX, QXD, Qx, QxD);
		(d, opp) := makeIntegral a;	-- opp = d * a is in Q[x][D]
		(l, op) := makez0 opp;		-- op = l * d * a is in Z[x][D]
		(den, num) := particularSolution(op, Qx2Zx((l::Q) * d * q));
		failed? num => empty;
		(nd, dd) := expandFraction den;
		[(retract(num) * makeRational(dd) / makeRational(nd))::QxD];
	}

	polynomialSolution(a:%, b:%):Partial % == {
		import from Z, QX, Qx, QxD;
		lodo? a and lodo? b and (zero?(l:=lodo b) or zero? degree l) =>
				[per [polsol(lodo a, leadingCoefficient l)]];
		failed;
	}

	local polsol(a:QxD, f:Qx):V QxD == {
		import from Z, Q, QX, Partial QX, QXD, QxD;
		import from LinearOrdinaryOperatorPolynomialSolutions(Z, Q,_
							coerce, ZX, ZXD, QX);
		import from UAF(QX, QXD, Qx, QxD);
		TRACE("multlodo::polsol: a = ", a);
		TRACE("multlodo::polsol: f = ", f);
		(d, opp) := makeIntegral a;	-- opp = d * a is in Q[x][D]
		f := d * f;			-- new eq is: opp(y) = f
		degree(df := denominator f) > 0 => empty;	-- no solution
		(l, op) := makez0(df * opp);	-- op = l df d a is in Z[x][D]
		u := particularSolution(op, (l::Q) * numerator f);
		failed? u => empty;				-- no solution
		[retract(u)::Qx::QxD]
	}

	exponentialSolutions(a:%):Partial % == {
		lodo? a => [per [expsols lodo a]];
		failed;
	}

	coerce(m:M Qx):% == {
		import from I, QxY, M QxY;
		(r, c) := dimensions m;
		a:M QxY := zero(r, c);
		for i in 1..r repeat for j in 1..c repeat a(i,j) := m(i,j)::QxY;
		a::%;
	}

	local fmat(a:%):Partial M Qx == {
		import from Boolean, I, Z, QxY, M Qx, M QxY;
		mat? a => {
			(r, c) := dimensions(m := mat a);
			mm:M Qx := zero(r, c);
			for i in 1..r repeat for j in 1..c repeat {
				(~zero?(p := m(i,j))) and degree(p) > 0 =>
					return failed;
				mm(i, j) := leadingCoefficient p;
			}
			[mm];
		}
		failed;
	}

#if FORALATERVERSION
	list(l:List %):Partial % == {
		TRACE("bernina::list, l = ", l);
		import from I, QxY, V QxY, Partial Qx;
		v:V QxY := zero(n := #l);
		zero? n => [per [v]];
		failed?(u := frac first l) => {
			darb? first l => matrix(l, n, #(darb first l));
			failed;
		}
		i:I := 1;
		v.i := retract(u)::QxY;
		for f in rest l repeat {
			failed?(u := frac f) => return failed;
			i := next i;
			v.i := retract(u)::QxY;
		}
		[per [v]];
	}

	local matrix(l:List %, r:I, c:I):Partial % == {
		import from I, QxY, V QxY, M QxY;
		m:M QxY := zero(r, c);
		i:I := 1;
		for f in l repeat {
			~(darb? f) => return failed;
			v := darb f;
			assert(#v = c);
			for j in 1..c repeat m(i, j) := v.j;
			i := next i;
		}
		[m::%];
	}
#endif

	system(n:I, l:List %):Partial % == {
		import from Boolean, QxY, M QxY, Partial Qx;
		(square?, m) := nthRoot(n, 2);
		~square? => failed;
		A:M QxY := zero(m, m);
		for i in 1..m repeat for j in 1..m repeat {
			failed?(u := frac first l) => return failed;
			A(i, j) := retract(u)::QxY;
			l := rest l;
		}
		[A::%];
	}

	system(a:%):Partial % == {
		import from I, Z, Qx, QxD, M Qx, List %;
		lodo? a => {
			zero?(L := lodo a)  => system(0, empty);
			zero? degree L => system(1, [a]);
			[(transpose companion lodonormal L)::%];
		}
		failed;
	}

	local lodoOrMatModp(a:%, b:%, f:(ZXD, PrimeFieldCategory) -> %,
				g:(M Zx, PrimeFieldCategory) -> %):Partial % == {
		import from Z, Partial Z, Partial M Qx;
		failed?(u := integer b) or (n := retract u) < 2 => failed;
		lodo? a => [f(makez makepoly(QXD, QxD, lodo a), field n)];
		failed?(m := fmat a) => failed;
		[g(MQx2MZx retract m, field n)];
	}

	eigenring(a:%):Partial % == {
		import from Partial M Qx;
		lodo? a => [per [eigen makez makepoly(QXD, QxD, lodo a)]];
		failed?(m := fmat a) => failed;
		[eigen(MQx2MZx retract m)::%];
	}

	kernel(a:%):Partial % == {
		import from QX, Partial M Qx;
		lodo? a => [per [kernel(lodo a, 0)]];
		failed?(m := fmat a) => failed;
		failed?(u := kernel(retract m, 0)) => failed;
		[retract(u)::%];
	}

	local fracgcd(a:Qx, b:Qx):Partial % == {
		import from QX;
		fracpoly(a, b, gcd);
	}

	local fraclcm(a:Qx, b:Qx):Partial % == {
		import from QX;
		fracpoly(a, b, lcm);
	}

	symmetricKernel(a:%, b:%):Partial % == {
		import from Boolean, Z, Partial Z, Qx;
		(~lodo? a) or failed?(u := integer b)
					or (n := retract u) <= 0 => failed;
		[per [symker(lodo a, n)]];
	}

	degree(a:%):Partial % == {
		lodo? a => lododegree lodo a;
		failed;
	}

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

	solve2(a:%):Partial % == {
		import from Z, Q, QX, Qx, QxY, List QxY;
		import from ORDER2, IRRSOL2, SOL2;
		(~lodo? a) or ((d := degree(L := lodo a)) ~= 2) => failed;
		sol := solve makez makepoly(QXD, QxD, L);
		sol case red => [per [[p for p in sol.red]]];
		isol := sol.irr;
		[per [[isol.grp::Z::QxY, isol.exp::QxY,
				isol.const::QX::Qx::QxY, isol.pullback::QxY]]];
	}

	irreducible3(a:%, b:%):Partial % == {
		import from I, Z, Q, M Q, Partial Z, Partial ZXD, Zx, QxY;
		import from ORDER3, ALGRIC, SOLUTION;
		(~lodo? a) or ((d := degree(L := lodo a)) ~= 3)
				or failed?(u := integer b) => failed;
		L2 := makez makepoly(QXD, QxD, L);
		group? := ~zero?(retract u);
		(s, group, sol) := solveIrreducible(L2, group?);
		if ~zero? s then group := -group;
		t := Zx2Qx s; 
		group? => [group::Z::%];
		sol case ratric => {
			zero?(sol.ratric) => [group::Z::%];
			[per [[group::Z::QxY, translate(sol.ratric,t)]$V(QxY)]];
		}
		sol case algric => {	-- encode as [group, modulus, den, num]
			aric := sol.algric;
			v:V(QxY) := zero(4 + machine degree(aric.num));
			v.1 := group::Z::QxY;
			v.2 := (aric.modulus)::Qx::QxY;
			v.3 := aric.den;
			for trm in aric.num repeat {
				(p, n) := trm;
				v(4 + machine n) := translate(p, t);
			}
			[per [v]];
		}
		if sol case radinv then {  -- case of G168xC3, radical invariant
			assert(abs(group) = 11);
			rinv := sol.radinv;
			ivs := invariants rinv;
			exp := exponential rinv;	-- cannot be an integer
		}
		else {			-- other groups with invariant
			ivs := sol.inv;
			exp := group::Z::Qx;
		}
		iv := polynomial ivs;
		can := canonicalImage ivs;
		(r, c) := dimensions iv;
		assert(c > 0);
		local m:M QxY;
		m := zero(r + 1, 2 * c + 1);	-- last column is for t
		encodeSemiInvariant!(m,polynomial ivs,canonicalImage ivs,exp,0);
		m(1, 2 * c + 1) := t::QxY;
		[m::%];
	}

	symmetricSquareRoot(a:%):Partial % == {
		import from Z, Q, Partial ZXD, ORDER3;
		(~lodo? a) or ((d := degree(L := lodo a)) ~= 3) => failed;
		L2 := makez makepoly(QXD, QxD, L);
		failed?(u := symmetricSquareRoot L2) => [0];
		[makefrac(QXD, QxD, ZXD2QXD retract u)::%];
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
		import from Q, ORDER2;
		decompose0(a, decompose L);
	}

	local decompose3(a:%, L:ZXD):% == {
		import from Q, ORDER3;
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
		h := u.alg.modulus::Qx::QxY;
		unum := numerator(u.alg.c0);
		uden := denominator(u.alg.c0);
		zero? #(v := u.alg.ratpart) => per [[h, unum, uden]];
		assert(one? #v);
		per [[h, unum, uden, QxD2QxY(v.1)]];
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
		import from Q, ORDER2;
		factor0(a, c1, c2, factorDecomp L);
	}

	local factor3(a:%, L:ZXD, c1:QX, c2:Z):% == {
		import from Q, ORDER3;
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
		md := prev(-m)::Z::QxY;
		h := algrec.modulus::Qx::QxY;
		unum := numerator(algrec.c0);
		uden := denominator(algrec.c0);
		zero? #(v := algrec.ratpart) => {
			assert(zero? m);
			per [[md, h, unum, uden]];
		}
		assert(m = 0 or m = 3 or m = 4);
		if ~zero?(m) then v.1 := inv((c2 * c1)::Qx) * v.1;
		v1 := QxD2QxY(v.1);
		m = 4 => {
			assert(#v = 2);
			per [[md, h, unum, uden, v1, QxD2QxY(v.2)]];
		}
		assert(#v = 1);
		per [[md, h, unum, uden, v1]];
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

	kernel(a:%, b:%):Partial % == {
		import from Z, Q, QX, Qx, Partial Z, Partial Qx, Partial M Qx;
		failed?(u := frac b) or
			degree(d := denominator(f := retract u)) > 0 => failed;
                sing := inv(leadingCoefficient d) * numerator f;
		lodo? a => [per [kernel(lodo a, sing)]];
		failed?(m := fmat a) => failed;
		failed?(ans := kernel(retract m, sing)) => failed;
		[retract(ans)::%];
	}

#if LATER
	parametricKernel(a:%, g:List %):Partial % == {
		import from I, Z, V Qx;
		lodo? a => {
			rh:V Qx := zero(n := #g);
			for i in 1..n for h in g repeat {
				if lodo? h and
					(zero?(q := lodo h) or zero? degree q)
						then rh.i:=leadingCoefficient q;
				else return failed;
			}
			[kernel(lodo a, rh)::%];
		}
		failed;
	}

	kernel(a:%, d:List %, b:%):Partial % == {
		import from I, Z, Partial Z, Qx, V QX, SYS Qx, Partial M Qx;
		import from M Qx, LODSRationalSolutions(Q, QX);
		failed?(m := fmat a) => failed;
		n := rows(A := retract m);
		T:V QX := zero n;
		for i in 1..n for p in d repeat
			T.i := numerator leadingCoefficient lodo p;
		[rationalKernel(system(1, A), T, retract integer b)::%];
	}
#endif

	D(a:%, b:%):Partial % == {
		import from Z, Partial Z, Qx, Partial Qx;
		failed?(ua := frac a) or
			failed?(ub := integer b) or (n := retract ub) < 0 =>
				failed;
		[differentiate(retract ua, n)::QxD::%];
	}

	apply(a:%, b:%):Partial % == {
		import from Z;
		lodo? a and lodo? b and (zero?(q:=lodo b) or zero? degree q) =>
				[(lodo(a)(leadingCoefficient q))::QxD::%];
		failed;
	}

	(a:%) = (b:%):Boolean == {
		import from V QxD, M QxY;
		lodo? a => lodo? b and lodo a = lodo b;
		vec? a => vec? b and vec a = vec b;
		mat? a => mat? b and mat a = mat b;
		darb? a and darb? b and darb a = darb b;
	}

	extree(a:%):ExpressionTree == {
		import from V QxD, M QxY;
		lodo? a => extree lodo a;
		vec? a => extree vec a;
		darb? a => extree darb a;
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
		import from I, Z, Partial Z, Qx, Partial Qx, M QxY;
		failed?(u := integer b) => failed;
		(n := retract u) < 0 => {
			failed?(ua := frac a) => failed;
			[(retract(ua)^n)::QxD::%];
		}
		lodo? a => [(lodo(a)^n)::%];
		mat? a => [(mat(a)^(machine n))::%];
		failed;
	}

	adjoint(a:%):Partial % == {
		lodo? a => [adjoint(lodo a)::%];
		mat? a => [(- transpose(mat a))::%];
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

	Darboux(a:%):Partial % == {
		TRACE("bernina::Darboux ", a);
		import from Boolean, Z, Q, QxD, V QxY, List QxY, ORDER2;
		~lodo?(a) or degree(L := lodo a) ~= 2 => failed;
		op := makez makepoly(QXD, QxD, L);
		TRACE("op ", "computed");
		K := Darboux op;
		TRACE("Darboux curves = ", K);
		[per [[p for p in K]]];
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

	symPower(a:%, b:%):Partial % ==
		lodoposmat(a, b, symmetricPowerSystem$QxD);

	extPower(a:%, b:%):Partial % ==
		lodoposmat(a, b, exteriorPowerSystem$QxD);

	radicalInvariants(a:%, b:%):Partial % == {
		import from Z;
		lodonpos(a, b, 1, rinvar0);
	}

	radicalInvariants(a:%, b:%, c:%):Partial % == {
		import from Z, Partial Z;
		(~lodo? a) or failed?(u := integer b) or (n := retract u) < 1
			or failed?(v := integer c) or (m := retract v) < 0 =>
									failed;
		[rinvar(lodo a, n, m)];
	}

	local rinvar0(a:QxD, n:Z):% == rinvar(a, n, 0);

	local rinvar(a:QxD, n:Z, order:Z):% == {
		import from Q, M Q, INVAR, RINVAR, List RINVAR;
		L := makez makepoly(QXD, QxD, a);
		empty?(siv := radicalInvariants(L, n, order)) => zero(0, 0)::%;
		dim:I := 0;
		for iv in siv repeat dim := dim + dimension invariants iv;
		r := numberOfRows polynomial invariants first siv;
		m:M QxY := zero(r + 1, 2 * dim);
		base:I := 0;
		for iv in siv repeat {
			invs := invariants iv;
			base := encodeSemiInvariant!(m, polynomial invs,
							canonicalImage invs,
							exponential iv, base);
		}
		m::%;
	}

	local encodeSemiInvariant!(m:M QxY, pl:M Q, can:M Qx, exp:Qx, b:I):I=={
		import from QX, QxY;
		(r, c) := dimensions pl;
		for j in 1..c repeat {
			for i in 1..r repeat {
				m(i, b + 2*j-1) := pl(i, j)::QX::Qx::QxY;
				m(i, b + 2 * j) := can(i, j)::QxY;
			}
			m(r + 1, b+2*j-1) := exp::QxY;
		}
		b + 2*c;
	}

	semiInvariants(a:%, b:%):Partial % == {
		import from Z;
		lodonpos(a, b, 1, sinvar);
	}

	local sinvar(a:QxD, n:Z):% == {
		import from Q, M Q, SINVAR, List SINVAR;
		L := makez makepoly(QXD, QxD, a);
		empty?(siv := semiInvariants(L, n)) => zero(0, 0)::%;
		dim:I := 0;
		for iv in siv repeat dim := dim + dimension iv;
		r := numberOfRows polynomial first siv;
		m:M QxY := zero(r + 1, 2 * dim);
		base:I := 0;
		for iv in siv repeat
			base := encodeSemiInvariant!(m, polynomial iv,
							canonicalImage iv,
							exponential iv, base);
		m::%;
	}

	invariants(a:%, b:%):Partial % == {
		import from Z;
		-- TEMPORARY: ALLOW FOR b < 0 TO TEST HEURISTIC
		-- lodonpos(a, b, 1, invar);
		import from Partial Z;
		(~lodo? a) or failed?(u := integer b)
			or zero?(n := retract u) => failed;
		[invar(lodo a, n)];
	}

	-- TEMPO: n < 0 ==> USE CANDIDATE INVARIANTS ONLY
	local invar(a:QxD, n:Z):% == {
		import from I, Q, M Q, QX, Zx, Qx, QxY, INVAR;
		assert(~zero? n);
		local den:PZX;
		local num:V QX;
		local can:M Qx;
		L := makez makepoly(QXD, QxD, a);
		if n < 0 then (den, num, iv) := candidateInvariants(L, -n);
		else {
			invs := invariants(L, n);
			iv := polynomial invs;
			can := canonicalImage invs;
		}
		(r, c) := dimensions iv;
		zero? c => (zero(0, 0)@M(QxY))::%;
		if n < 0 then {
			can := zero(r, c);
			(nd, dd) := expandFraction den;
			invden := Zx2Qx(dd / nd);
			for j in 1..c repeat can(1, j) := num.j * invden;
		}
		m:M QxY := zero(r + 1, 2 * c);
		encodeSemiInvariant!(m, iv, can, 0, 0);
		m::%;
	}

	dualFirstIntegral(a:%, b:%):Partial % == {
		import from Z;
		lodonpos(a, b, 1, dualFirst);
	}

	local dualFirst(a:QxD, n:Z):% == {
		import from I, Q, INVAR;
		L := makez makepoly(QXD, QxD, a);
		symmetricKernel(invariants(L, n))::%;
	}

	local lodonpos(a:%, b:%, min:Z, f:(QxD,Z) -> %):Partial % == {
		import from Boolean, Z, Partial Z;
		TRACE("lodonpos:a = ", a);
		TRACE("lodonpos:b = ", b);
		TRACE("lodonpos:min = ", min);
		(~lodo? a) or failed?(u := integer b)
			or (n := retract u) < min => failed;
		TRACE("lodonpos: ", "input ok, calling f");
		[f(lodo a, n)];
	}

	local expsols(a:QxD):V QxY == {
		import from Q, List Cross(Qx, PQX, V QX),
			LinearOrdinaryDifferentialOperatorExponentialSolutions(_
							Z,Q,coerce,ZX,ZXD,QX);
		op := makez makepoly(QXD, QxD, a);
		[expsol2poly t for t in exponentialSolutions op];
	}

	-- (u, d,[v1,...,vm]) corresponds to the sol exp(int u) \sum_i ci vi/d
	-- returns the poly  u + v1/d y + ... + vm/d y^m
	local expsol2poly(u:Qx, den:PQX, num:V QX):QxY == {
		import from I, Z, V QxD, QxD, QxY;
		(nd, dd) := expandFraction den;
		v := vecnormal(nd, dd, num);    -- V(QxD) of order 0 here
		q := u::QxY;
		for i in #v..1 by -1 repeat
			q := add!(q, leadingCoefficient(v.i), i::Z);
		q;
	}

	local radsols(a:QxD, n:Z):% == {
		import from Q, V QxY, List Cross(List Cross(Q, ZX), PZX, V QX),
			LinearOrdinaryDifferentialOperatorRegularSolutions(Z,_
							Q,coerce,ZX,ZXD,QX);
		op := makez makepoly(QXD, QxD, a);
		m:I := 0;
		r:I := 0;
		l:List V QxY := empty;
		for t in radicalSolutions(op, n) repeat {
			v := radsol2vec t;
			if m < #v then m := #v;
			l := cons(v, l);
			r := next r;
		}
		mat:M QxY := zero(r, m);
		for i in 1..r repeat {
			v := first l; l := rest l;
			for j in 1..#v repeat mat(i, j) := v.j;
		}
		assert(empty? l);
		per [mat];
	}

	-- rad = [(p1,e1),...,(pn,en)] = p1^e1,...,pn^en
	-- (d,[v1,...,vm]) corresponds to the basis v1/d,...,vm/d
	-- returns a vector of the form
	-- [e1 + p1 y + ... + en y^(2n-2) + pn y^(2n-1), v1/d, ..., vm/d]
	local radsol2vec(rad:List Cross(Q, ZX), den:PZX, num:V QX):V QxY == {
		import from I, Z, V QxD, QxD, QxY;
		v := vecnormal(den, num);    -- V(QxD) of order 0 in that case
		w:V QxY := zero(next(#v));
		w.1 := radsol2poly rad;
		for i in 1..#v repeat w(next i) := leadingCoefficient(v.i)::QxY;
		w;
	}

	-- rad = [(p1,e1),...,(pn,en)] = p1^e1,...,pn^en
	-- returns(e1 + p1 y + ... + en y^(2n-2) + pn y^(2n-1))
	local radsol2poly(rad:List Cross(Q, ZX)):QxY == {
		import from QX, Qx, UAF(Z, ZX, Q, QX);
		i:Z := 0;
		n := (#rad)::Z;
		assert(n > 0);
		nn := n + n;
		q:QxY := monomial nn;
		for pair in rad repeat {
			(e, p) := pair;
			q := add!(q, e::QX::Qx, i);
			i := next i;
			q := add!(q, makeRational(p)::Qx, i);
			i := next i;
		}
		assert(i = nn);
		add!(q, -1, nn);
	}

	local lodoposmat(a:%, b:%, f:(QxD, Z) -> SYS Qx):Partial % == {
		import from Z;
		lodonpos(a, b, 0, lodopmat f);
	}

	local SYS2B(L:SYS Qx):M Qx == {
		import from Qx, V Qx;
		(c, A) := matrix L;
		diagonal([inv g for g in c]) * A;
	}

	local lodopos(a:%, b:%, f:(QxD, Z) -> QxD):Partial % == {
		import from Z;
		lodonpos(a, b, 0, (L:QxD, n:Z):% +-> f(L, n)::%);
	}

	local extpow(a:QxD, n:Z):QxD == {
		import from ZXD;
		makefrac(QXD, QxD,
			ZXD2QXD exteriorPower(makez makepoly(QXD, QxD, a), n));
	}

	local sympow(a:QxD, n:Z):QxD == {
		import from ZXD;
		makefrac(QXD, QxD,
			ZXD2QXD symmetricPower(makez makepoly(QXD, QxD, a), n));
	}

	makeIntegral(a:%):Partial % == {
		lodo? a => [makefrac(QXD, QxD, makepoly(QXD,QxD,lodo a))::%];
		darb? a => [per [makepoly darb a]];
		failed;
	}

	normalize(a:%):Partial % == {
		import from I, V QxD;
		lodo? a => [lodonormal(lodo a)::%];
		vec? a => [per [vecnormal! copy vec a]];
		u:V QxY := zero(#(t := darb a));
		for i in 1..#t repeat u.i := xynormal(t.i);
		[per [u]];
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
		import from UAF(Z, ZX, Q, QX);
		(c, b) := normalize a;
		b;
	}

	local fracnormal(a:Qx):Qx ==
		polynormal numerator a / polynormal denominator a;

	local polynormal(a:QX):QX == {
		import from Z, Q;
		zero? a => a;
		zero? degree a => 1;
		inv(leadingCoefficient a) * a;
	}

	local xynormal(a:QxY):QxY == {
		import from Z, Qx;
		zero? a => a;
		c := leadingCoefficient a;
		zero? degree a => fracnormal(c)::QxY;
		inv(c) * a;
	}

	local makefrac(QXY:MonogenicAlgebra QX,_
		QxY:MonogenicAlgebra Qx, a:QXY):QxY == {
		import from UAF(QX,QXY,Qx,QxY);
		makeRational a;
	}

	local makepoly(v:V QxY):V QxY == {
		import from I;
		w:V QxY := zero(n := #v);
		for i in 1..n repeat
			w.i := makefrac(QXy, QxY, makepoly(QXy, QxY, v.i));
		w;
	}

	local makepoly(QXY:MonogenicAlgebra QX,_
		QxY:MonogenicAlgebra Qx, a:QxY):QXY == {
		import from UAF(QX, QXY, Qx, QxY);
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

	local extker(a:QxD, n:Z):% == {
		import from Q, QX, Qx, M QX, EXTKER, List EXTKER;
		L := makez makepoly(QXD, QxD, a);
		empty?(xker := exteriorKernel(L, n)) => (zero(0,0)$M(Qx))::%;
		dim:I := 0;
		for iv in xker repeat dim := dim + dimension iv;
		r := numberOfRows numerator first xker;
		m:M Qx := zero(r + 1, dim);
		for iv in xker repeat {
			exp := exponential iv;
			invden := inv(denominator(iv)::Qx);
			num := numerator iv;
			c := numberOfColumns num;
			for j in 1..c repeat {
				lc:Q := 0;
				for i in 1..r while zero? lc repeat
					lc := leadingCoefficient num(i,j);
				assert(~zero? lc);
				invlc := inv lc;
				for i in 1..r repeat
					m(i,j) := (invlc * num(i,j)) * invden;
				m(r + 1, j) := exp;
			}
		}
		m::%;
	}

	local eigen(op:ZXD):V QxD == {
		import from I, Q, V QXD, Qx, Product ZX;
		import from EIGEN(Z, Q, coerce, ZX, ZXD, QX, QXD);
		import from UAF(Z, ZX, Q, QX), UAF(QX, QXD, Qx, QxD);
		(den, num) := eigenring op;
		v:V QxD := zero(n := #num);
		if n > 0 then {
			d := inv(makeRational(expand den)::Qx);
			for i in 1..n repeat v.i := d * num.i;
		}
		v;
	}

	local eigen(A:M Zx):M QxY == {
		import from Q, SYS ZX, EIGEN(Z, Q, coerce, ZX, ZXD, QX, QXD);
		assert(square? A);
		(den, num) := eigenring system A;
		encodeEigenring(numberOfRows A, den, num);
	}

	local encodeEigenring(n:I, den:ZX, num:V M QX):M QxY == {
		import from Qx, QxY, M QX, UAF(Z, ZX, Q, QX);
		dim := #num;
		d:QX := { dim > 0 => makeRational den; 1 }
		m:M QxY := zero(n, n * dim);
		for k in 1..dim repeat {
			c := prev(k) * n;
			for i in 1..n repeat for j in 1..n repeat
				m(i, j + c) := (num(k)(i, j) / d)::QxY;
		}
		m;
	}

	local MQx2MZx(A:M Qx):M Zx == {
		import from I;
		(r, c) := dimensions A;
		B:M(Zx) := zero(r, c);
		for i in 1..r repeat for j in 1..c repeat
			B(i, j) := Qx2Zx A(i, j);
		B;
	}

	-- second argument is characteristic if it is an integer > 1
	local kernel(A:M Qx, sing:QX):Partial M Qx == {
		import from I, Z, Q, Qx, ZX, M QX, UAF(Z, ZX, Q, QX);
		import from SYS ZX,
			LinearOrdinaryDifferentialSystemRationalSolutions(Z,_
							Q, coerce, ZX, ZXD, QX);
		(den, num) := {
			zero? sing => kernel system MQx2MZx A;
			zero? degree sing => {
				q := leadingCoefficient sing;
				one?(denominator q)
					and (charac := numerator q) > 1 =>
						(1$ZX, kernel(system MQx2MZx A,
								field charac));
				-- TEMPORARY: ONLY CHARAC SUPPORTED AS 2ND ARG
				(0$ZX, zero(0,0)$M(QX));
			}
			-- TEMPORARY: ONLY CHARAC SUPPORTED AS 2ND ARGUMENT
			(0$ZX, zero(0,0)$M(QX));
		}
		-- TEMPORARY: ONLY CHARAC SUPPORTED AS 2ND ARGUMENT
		zero? den => failed;
		(r, c) := dimensions num;
		d:QX := { c > 0 => makeRational den; 0 }
		ans:M Qx := zero(r, c);
		for i in 1..r repeat for j in 1..c repeat
			ans(i, j) := num(i, j) / d;
		[ans];
	}

	local kernel(L:SYS ZX, Fp:PrimeFieldCategory):M QX == {
		import from I, Fp, Q, M FpX, SYS FpX;
		import from MonogenicAlgebra2(Z, ZX, Fp, FpX);
		import from MonogenicAlgebra2(Fp, FpX, Q, QX);
		import from LinearOrdinaryFirstOrderSystem2(ZX, FpX),
		    LinearOrdinaryDifferentialSystemModularRationalSolutions(_
									Fp, FpX);
		modp:ZX -> FpX := map(coerce$Fp);
		k := kernel(map(modp)(L));
		rat:FpX -> QX := map((f:Fp):Q +-> lift(f)::Q);
		(r, c) := dimensions k;
		mq:M QX := zero(r, c);
		for i in 1..r repeat for j in 1..c repeat mq(i,j):= rat k(i,j);
		mq;
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

	local symker(a:QxD, n:Z):V QxD == {
		import from Q, INVAR;
		op := makez makepoly(QXD, QxD, a);
		vecnormal symmetricKernel(op, n);
	}

	-- |second argument| is characteristic if it is an integer > 1
	-- use modular ABP if second argument is < -1, linear system if > 1
	local kernel(a:QxD, sing:QX):V QxD == {
		import from Z, Q, V QX, Partial V QX, Qx;
		import from UAF(Z, ZX, Q, QX), RATSOL;
		TRACE("multlodo::kernel, a = ", a);
		TRACE("multlodo::kernel, sing = ", sing);
		opq := makepoly(QXD, QxD, a);
		op := makez opq;
		zero? sing => vecnormal kernel op;
		zero? degree sing => {
			q := leadingCoefficient sing;
			one? denominator q => {	
				charac := abs(nq := numerator q);
				charac > 1 => kernel(op, field charac, nq > 0);
				nq = -1 => {	-- poly sols, modular method
					failed?(u := kernel(op)$MODSOL) =>
						vecnormal kernel(op, 1$ZX);
					vecnormal(1, 1, retract u);
				}
				vecnormal kernel(op, 1$ZX);
			}
			vecnormal kernel(op, 1$ZX);
		}
		(c, p) := makeIntegral sing;
		vecnormal kernel(op, p);
	}

	local field(p:Z):SmallPrimeFieldCategory == {
		import from I;
		assert(p > 1);
		p = 2 => PrimeField2;
		p < 10007 => ZechPrimeField machine p;
		SmallPrimeField machine p;
	}

	local pCurvOp(op:ZXD, Fp:PrimeFieldCategory):% == {
		import from Qx, QxD, FpXD, MonogenicAlgebra2(Z, ZX, Fp, FpX),
				MonogenicAlgebra2(Fp, FpX, Q, QX),
				MonogenicAlgebra2(ZX, ZXD, FpX, FpXD),
				MonogenicAlgebra2(FpX, FpXD, Qx, QxD);
		opf := map(map(coerce$Fp))(op);		-- op in FpXD;
		(r, pc) := pCurvature opf;
		local Fp2Q(f:Fp):Q == lift(f)::Q;
		local FpX2Qx(p:FpX):Qx == map(Fp2Q)(p) :: Qx;
		(inv(FpX2Qx r) * map(FpX2Qx)(pc))::%;
	}

	local eigenOp(op:ZXD, Fp:PrimeFieldCategory):% == {
		local idf(f:Fp):Fp == f;
		import from Fp, V FpXD, MonogenicAlgebra2(Z, ZX, Fp, FpX),
				MonogenicAlgebra2(Fp, FpX, Q, QX),
				MonogenicAlgebra2(ZX, ZXD, FpX, FpXD),
				MonogenicAlgebra2(FpX, FpXD, Qx, QxD);
		import from EIGEN(Fp, Fp, idf, FpX, FpXD, FpX, FpXD);
		opf := map(map(coerce$Fp))(op);		-- op in FpXD;
		(den, num) := eigenring opf;		-- den is always 1
		local Fp2Q(f:Fp):Q == lift(f)::Q;
		local FpX2Qx(p:FpX):Qx == map(Fp2Q)(p) :: Qx;
		per [[map(FpX2Qx)(p) for p in num]];
	}

	local pCurvSys(A:M Zx, Fp:PrimeFieldCategory):% == {
		macro Fpx == Fraction FpX;
		assert(square? A);
		import from SYS FpX;
		import from MatrixCategory2(Zx, M Zx, Fpx, M Fpx),
				MatrixCategory2(FpX, M FpX, QX, M QX),
				LinearOrdinaryFirstOrderSystem2(FpX, Qx);
		local ZX2FpX:ZX->FpX== map(coerce$Fp)$MonogenicAlgebra2(Z,ZX,Fp,FpX);
		local Zx2Fpx(f:Zx):Fpx== ZX2FpX(numerator f) / ZX2FpX(denominator f);
		pc := pCurvature(system(map(Zx2Fpx)(A)), derivation$FpX);
		local Fp2Q(f:Fp):Q == lift(f)::Q;
		local FpX2QX:FpX->QX == map(Fp2Q)$MonogenicAlgebra2(Fp, FpX, Q, QX);
		local FpX2Qx(f:FpX):Qx== FpX2QX(f)::Qx;
		SYS2B(map(FpX2Qx)(pc))::%;
	}

	local eigenSys(A:M Zx, Fp:PrimeFieldCategory):% == {
		macro Fpx == Fraction FpX;
		local idf(f:Fp):Fp == f;
		assert(square? A);
		import from Fp, ZX, QX, SYS FpX, V M QX;
		import from MonogenicAlgebra2(Fp, FpX, Q, QX);
		import from MatrixCategory2(Zx, M Zx, Fpx, M Fpx),
				MatrixCategory2(FpX, M FpX, QX, M QX);
		import from EIGEN(Fp, Fp, idf, FpX, FpXD, FpX, FpXD);
		local ZX2FpX:ZX->FpX== map(coerce$Fp)$MonogenicAlgebra2(Z,ZX,Fp,FpX);
		local Zx2Fpx(f:Zx):Fpx== ZX2FpX(numerator f) / ZX2FpX(denominator f);
		e:V M FpX := eigenring system(map(Zx2Fpx)(A));
		local Fp2Q(f:Fp):Q == lift(f)::Q;
		encodeEigenring(numberOfRows A,1,[map(map(Fp2Q))(t) for t in e])::%;
	}

	local kernel(op:ZXD, Fp:PrimeFieldCategory, linsys?:Boolean):V QxD == {
		macro {
			FpXE == LinearOrdinaryRecurrence(Fp, FpX);
			MODRATSOL == _
			LinearOrdinaryDifferentialOperatorModularRationalSolutions;
		}
		local idf(f:Fp):Fp == f;
		import from Q, Fp, V FpX, MonogenicAlgebra2(Z, ZX, Fp, FpX),
				MonogenicAlgebra2(Fp, FpX, Z, ZX),
				MonogenicAlgebra2(ZX, ZXD, FpX, FpXD),
				MonogenicAlgebra2(ZX, ZXE, FpX, FpXE),
				LinearOrdinaryOperatorPolynomialSolutions(_
							Z,Q,coerce,ZX,ZXD,QX),
				LinearOrdinaryOperatorPolynomialSolutions(_
							Fp,Fp,idf,FpX,FpXD,FpX);
		local v:V FpX;
		opf := map(map(coerce$Fp))(op);		-- op in FpXD;
		if linsys? then v := kernel(opf)$MODRATSOL(Fp, FpX, FpXD);
		else {
			(c, L) := primitive op;
			(r, e, n, bd) := bound L;
			v := kernel(map(map(coerce$Fp))(r), e, n, bd);
		}
		[ZX2QxD(map(lift)(p)) for p in v];
	}

	local ZX2QxD(p:ZX):QxD == {
		import from Q, Qx, MonogenicAlgebra2(Z, ZX, Q, QX);
		map(coerce)(p)::Qx::QxD;
	}

	local maxdeg(v:V QX):Z == {
		import from Boolean, QX;
		n:Z := 0;
		for p in v repeat
			if ~zero?(p) and (d := degree p) > n then n := d;
		n;
	}

#if LATER
	local kernel(a:QxD, g:V Qx):M Qx == {
		import from I,V Zx,M Z,QX,Qx,LODORationalSolutions(Z, ZX, ZXD);
		import from UAF(QX, QXD, Qx, QxD);
		(d, opp) := makeIntegral a;	-- opp = d * a is in Q[x][D]
		(l, op) := makez0 opp;		-- op = l * d * a is in Z[x][D]
		d := l * d;
		gz:V Zx := zero(n := #g);
		for i in 1..n repeat gz.i := Qx2Zx(d * g.i);
		(h, s) := rationalKernel(op, gz);
		(r, c) := dimensions s;
		assert(c = n + #h);
		-- store h as extra row of s
		m:M Qx := zero(r1 := next r, c);
		for i in 1..r repeat for j in 1..c repeat m(i,j) := s(i,j)::Qx;
		for j in 1..#h repeat m(r1,j) := Zx2Qx(h.j);
		m;
	}

	local qkernel(a:QXD, sing:QX):V QxD == {
		import from I, V Qx, LODORationalSolutions(Q, QX, QXD);
		K := {
			zero? sing => rationalKernel a;
			rationalKernel(a, sing);
		}
		w:V QxD := zero(n := #K);
		for i in 1..n repeat w.i := (K.i)::QxD;
		w;
	}
#endif

	local vecnormal(den:PZX, v:V QX):V QxD == {
		import from UAF(Z, ZX, Q, QX);
		(nd, dd) := expandFraction den;
		vecnormal(makeRational nd, makeRational dd, v);
	}

	-- denominator is nd/dd, solution is then v dd / nd
	local vecnormal(nd:QX, dd:QX, v:V QX):V QxD == {
		import from I, Z, Qx;
		w:V QxD := zero(n := #v);
		invden := dd / nd;
		-- do not normalize large solutions (benchmarks!)
		normal? := maxdeg(v) < 30;
		for i in 1..n repeat {
			w.i := {
				normal? => fracnormal(v.i * invden)::QxD;
				(v.i * invden)::QxD;
			}
		}
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
