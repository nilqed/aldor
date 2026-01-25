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
------------------------   sit_matcat.as   -----------------------
-- Copyright (c) Marco Codutti 1995
-- Copyright (c) INRIA 1999, Version 0.1.12
-- Logiciel Sum^it ©INRIA 1999, dans sa version 0.1.12
-- Copyright (c) Swiss Federal Polytechnic Institute Zurich, 1995
-----------------------------------------------------------------------------

#include "sumit"

macro {
	I == MachineInteger;
	V == Vector;
}

#if ALDOC
\thistype{MatrixCategory}
\History{Marco Codutti}{12 may 95}{created}
\History{Manuel Bronstein}{1/12/1999}{redesigned}
\Usage{\this~R: Category}
\Params{
{\em R} & \astype{SumitType} & The coefficient domain\\
        & \astype{ArithmeticType} &\\
}
\Descr{\this~R is a common category for matrices of arbitrary sizes
with coefficients in R. They are $1$--indexed and whether they do
bound checking depends on each particular matrix type.}
\begin{exports}
\category{\astype{CopyableType}}\\
\category{\astype{LinearArithmeticType} R}\\
\asexp{$*$}: & (\%,V) $\to$ V & multiplication by a vector\\
\asexp{[]}: & \builtin{Tuple} V $\to$ \% & create a matrix\\
            & \astype{Generator} V $\to$ \% & \\
\asexp{apply}: & (\%,I,I) $\to$ R & extract an entry\\
\asexp{apply}: & (\%,I,I,I,I) $\to$ \% & extract a submatrix\\
\asexp{colCombine!}: & (\%,R,I,R,I) $\to$ \% &
In--place linear combination of columns\\ 
                     & (\%,R,I,R,I,I,I) $\to$ \% &\\
                     & (\%,(R,R)$\to$ R,I,I) $\to$ \%\\
                     & (\%,(R,R)$\to$ R,I,I,I,I) $\to$ \%\\
\asexp{colSwap!}: & (\%,I,I) $to$ \% & Swap columns in--place\\
                  & (\%,I,I,I,I) $to$ \% &\\
\asexp{column}: & (\%,I) $\to$ V & extraction of a column\\
\asexp{columns}: & \% $\to$ \astype{Generator} V & iteration over the columns\\
\asexp{companion}: & V $\to$ \% & creates a companion matrix\\
                   & (V, R) $\to$ \% & \\
\asexp{diagonal}: & V $\to$ \% & creates a diagonal matrix\\
\asexp{diagonal?}: & \% $\to$ \astype{Boolean} & test for a diagonal matrix\\
\asexp{dimensions}: & \% $\to$  (I,I) & get row and column dimensions\\
\asexp{map}: & (R $\to$ R) $\to$ V $\to$ \% & lift a mapping\\
\asexp{map}: & (R $\to$ R) $\to$ \% $\to$ \% & lift a mapping\\
\asexp{map!}: & (R $\to$ R) $\to$ \% $\to$ \% & lift a mapping\\
\asexp{numberOfColumns}: & \% $\to$ I & number of columns of the matrix\\
\asexp{numberOfRows}: & \% $\to$ I & number of rows of the matrix\\
\asexp{one}: & I $\to$ \% & identity matrix\\
\asexp{one?}: & \% $\to$ \astype{Boolean} & test for an identity matrix\\
\asexp{row}: & (\%,I) $\to$ V & extraction of a row\\
\asexp{rowCombine!}: & (\%,R,I,R,I) $\to$ \% &
In--place linear combination of rows\\ 
                     & (\%,R,I,R,I,I,I) $\to$ \% &\\
                     & (\%,(R,R)$\to$ R,I,I) $\to$ \%\\
                     & (\%,(R,R)$\to$ R,I,I,I,I) $\to$ \%\\
\asexp{rowSwap!}: & (\%,I,I) $to$ \% & Swap rows in--place\\
                  & (\%,I,I,I,I) $to$ \% &\\
\asexp{rows}: & \% $\to$ \astype{Generator} V & iteration over the rows\\
\asexp{set!}: & (\%,I,I,R) $\to$ R & set an entry in the matrix\\
\asexp{setMatrix!}: & (\%,I,I,\%) $\to$ \% & modify a submatrix of a matrix\\
\asexp{square?}: & \% $\to$ \astype{Boolean} & test for a square matrix\\
\asexp{tensor}: & (\%, \%) $\to$ \% & tensor product\\
\asexp{transpose}: & V \% $\to$ \% & transpose a vector\\
\asexp{transpose}: & \% $\to$ \% & transpose a matrix\\
\asexp{transpose!}: & \% $\to$ \% & transpose a matrix in--place\\
\asexp{zero}: & (I,I) $\to$ \% & create a zero matrix\\
\asexp{zero!}: & \% $\to$ () & make all the entries zero\\
\asexp{zero?}: & \% $\to$ \astype{Boolean} & test if all entries are zero\\
\end{exports}
\begin{exports}[if R has \astype{Ring} then]
\asexp{random}: & () $\to$ \% & create a random matrix\\
                & (I,I) $\to$ \% & \\
\end{exports}
\begin{exports}[if R has \astype{DifferentialRing} then]
\asexp{wronskian}: & V $\to$ \% & Wronskian matrix\\
\end{exports}
\begin{aswhere}
I &==& \astype{MachineInteger}\\
V  &==& \astype{Vector} R\\
\end{aswhere}
\begin{exports}[if $R$ has \astype{SerializableType} then]
\category{\astype{SerializableType}}\\
\end{exports}
#endif

define MatrixCategory(R: Join(ArithmeticType, SumitType)): Category ==
	Join(CopyableType, LinearArithmeticType R) with {
	if R has SerializableType then SerializableType;
	*:              (%,V R) -> V R;
#if ALDOC
\aspage{$*$}
\Usage{A \name~v}
\Signature{(\%,\astype{Vector} R)}{\astype{Vector} R}
\Params{
{\em A} & \% & a matrix\\
{\em v} & \astype{Vector} R & a vector\\
}
\Retval{Returns the vector $A v$.}
#endif
	bracket: Tuple V R -> %;
	bracket: Generator V R -> %;
#if ALDOC
\aspage{[]}
\Usage{[$v_1,\dots,v_n$]\\{}[v for v in g]}
\Signatures{
\name: & \builtin{Tuple} \astype{Vector} R $\to$ \%\\
\name: & \astype{Generator} \astype{Vector} R $\to$ \%\\
}
\Params{
$v_1,\dots,v_n$ & \astype{Vector} R & vectors\\
{\em g} &
\astype{Generator} \astype{Vector} R & an iterator producing vectors\\
}
\Retval{Returns the matrix whose $\sth{i}$ column is $v_i$, respectively
the $\sth{i}$ vector generated by $g$.}
#endif
	apply:          (%,I,I) -> R;
	apply:          (%,I,I,I,I) -> %;
#if ALDOC
\aspage{apply}
\Usage{\name(A,n,m)\\ \name(A,n,m,r,c)\\ A(n, m)\\ A(n, m, r, c)}
\Signatures{
\name: & (\%,\astype{MachineInteger},\astype{MachineInteger}) $\to$ R\\
\name: & (\%,\astype{MachineInteger},\astype{MachineInteger},
\astype{MachineInteger},\astype{MachineInteger}) $\to$ \%\\
}
\Params{
{\em A} & \% & A matrix\\
{\em n,m,r,c} & \astype{MachineInteger} & indices\\
}
\Retval{A(n,m) returns the entry of $A$ at its $\sth n$ row and $\sth m$
column, while A(n,m,r,c) returns the submatrix of $A$ having $A(m,n)$ in
its top--left corner and $r$ rows and $c$ columns.}
#endif
	colCombine!:	 (%,R,I,R,I) -> %;
	colCombine!:	 (%,R,I,R,I,I,I) -> %;
	colCombine!:    (%,(R,R)->R,I,I) -> %;
	colCombine!:    (%,(R,R)->R,I,I,I,I) -> %;
	rowCombine!:	 (%,R,I,R,I) -> %;
	rowCombine!:	 (%,R,I,R,I,I,I) -> %;
	rowCombine!:    (%,(R,R)->R,I,I) -> %;
	rowCombine!:    (%,(R,R)->R,I,I,I,I) -> %;
#if ALDOC
\aspage	{colCombine!,rowCombine!}
\astarget{colCombine!}
\astarget{rowCombine!}
\Usage{
colCombine!($A,c_1,j_1,c_2,j_2$)\\
colCombine!($A,c_1,j_1,c_2,j_2,i_1,i_2$)\\
colCombine!($A,f,j_1,j_2$)\\
colCombine!($A,f,j_1,j_2,i_1,i_2$)\\
rowCombine!($A,c_1,i_1,c_2,i_2$)\\
rowCombine!($A,c_1,i_1,c_2,i_2,j_1,j_2$)\\
rowCombine!($A,f,i_1,i_2$)\\
rowCombine!($A,f,i_1,i_2,j_1,j_2$)\\
}
\Signatures{
\name:& (\%, R, I, R, I) $\to$ \%\\
\name:& (\%, R, I, R, I, I, I) $\to$ \% \\
\name: & (\%,(R,R) $\to$ R, I, I) $\to$ \%\\
\name: & (\%, (R,R) $\to$ R, I, I, I, I) $\to$ \% \\
}
\begin{aswhere}
I &==& \astype{MachineInteger}\\
\end{aswhere}
\Params{
{\em A} & \% & A matrix\\
{\em f} & (R,R) $\to$ R & An binary operation on R\\
{\em c1}, {\em c2} & R & coefficients from R \\
{\em j1}, {\em j2} & \astype{MachineInteger} & column indices\\
{\em i1}, {\em i2} & \astype{MachineInteger} & row indices\\
}
\Descr{The $\sth{j_1}$ column (resp.~$\sth{i_1}$ row) of $A$ is replaced by
the result of applying $f$ pointwise to its $\sth{j_1}$ and $\sth{j_2}$
columns (resp.~$\sth{i_1}$ and $\sth{i_2}$ rows).
If the last 2 arguments $i_1,i_2$ (resp.~$j_1,j_2$) are present, then
this operation is applied only for rows $i_1$ to $i_2$ (resp.~columns
$j_1$ to $j_2$) inclusive.
The form with $c_1$ and $c_2$ is equivalent to the first one with
the function $f$ defined by $f(x_1,x_2) = c_1 x_1+c_2 x_2$.}
#endif
	colSwap!:	(%,I,I) -> %;
	colSwap!:	(%,I,I,I,I) -> %;
	rowSwap!:	(%,I,I) -> %;
	rowSwap!:	(%,I,I,I,I) -> %;
#if ALDOC
\aspage    {colSwap!,rowSwap!}
\astarget  {colSwap!}
\astarget  {rowSwap!}
\Usage{
colSwap!($A,j_1,j_2$)\\
colSwap!($A,j_1,j_2,i_1,i_2$)\\
rowSwap!($A,i_1,i_2$)\\
rowSwap!($A,i_1,i_2,j_1,j_2$)\\
\Signatures{
\name:& (\%, I, I) $\to$ \%\\
\name:& (\%, I, I, I, I) $\to$ \%\\
}
\begin{aswhere}
I &==& \astype{MachineInteger}\\
\end{aswhere}
\Params{
{\em A} & \% & A matrix\\
{\em j1}, {\em j2} & \astype{MachineInteger} & column indices\\
{\em i1}, {\em i2} & \astype{MachineInteger} & row indices\\
}
\Descr{The $\sth{j_1}$ and $\sth{j_2}$ columns (resp.~$\sth{i_1}$ and
$\sth{i_2}$ rows) of $A$ are exchanged in--place.
If the last 2 arguments $i_1,i_2$ (resp.~$j_1,j_2$) are present, then
this operation is applied only for rows $i_1$ to $i_2$ (resp.~columns
$j_1$ to $j_2$) inclusive.}
#endif
	column: (%, I) -> V R;
	row: (%, I) -> V R;
#if ALDOC
\aspage{column,row}
\astarget{column}
\astarget{row}
\Usage{column(A,n)\\ row(A,n)}}
\Signature{(\%,\astype{MachineInteger})}{\astype{Vector} R}
\Params{
{\em A} & \% & A matrix\\
{\em n} & \astype{MachineInteger} & An index\\
}
\Retval{Returns the $\sth{n}$ column (resp.~row) of A as a vector.}
#endif
	columns: % -> Generator V R;
	rows: % -> Generator V R;
#if ALDOC
\aspage{columns,rows}
\astarget{columns}
\astarget{rows}
\Usage{for v in columns~A repeat \{ \dots \}\\
for v in rows~A repeat \{ \dots \} }
\Signature{\%}{\astype{Generator} \astype{Vector} R}
\Params{{\em A} & \% & A matrix\\}
\Descr{This generator yields the columns (resp.~rows) of A in succession.}
#endif
	companion:	(V R, a:R == 1) -> %;
#if ALDOC
\aspage{companion}
\Usage{\name~$[r_1,\dots,r_n]$\\ \\name($[r_1,\dots,r_n],a$)}
\Signature{(\astype{Vector} R, R)}{\%}
\Params{
$r_1,\dots,r_n$ & R & Entries\\
{\em a} & R & A subdiagonal entry (optional, default is $1$)\\
}
\Retval{Returns the companion matrix
$$
\pmatrix{
0 &        &   &   &  r_1  \cr
a & \ddots &   &   &  r_2  \cr
  & \ddots &   &   &  r_3  \cr
  &        &   &   & \vdots\cr
  &        &   & a &  r_n  \cr
}
$$
}
\seealso{\asexp{diagonal}}
#endif
	diagonal:	V R -> %;
	diagonal?:	% -> Boolean;
#if ALDOC
\aspage{diagonal}
\astarget{\name?}
\Usage{\name~[$r_1,\dots,r_n$]\\ \name?~A}
\Signatures{
\name:  & \astype{Vector} R $\to$ \%\\
\name?: & \% $\to$ \astype{Boolean}\\
}
\Params{
$r_1,\dots,r_n$ & R & Entries\\
{\em A} & \% & A matrix\\
}
\Descr{\name([$r_1,\dots,r_n$]) returns a diagonal matrix whose diagonal
elements are $r_1,\dots,r_n$, while \name?(A) returns \true if {\em A}
is a diagonal matrix, \false otherwise.}
\seealso{\asexp{companion},\asexp{one?},\asexp{square?}}
#endif
	dimensions:     % -> (I,I);
#if ALDOC
\aspage    {dimensions}
\Usage     {\name~A}
\Signature {\%}{(\astype{MachineInteger},\astype{MachineInteger})}
\Params    {{\em A} & \% & A matrix\\}
\Retval    {The number of rows and columns in {\em A}}
\seealso   {\asexp{numberOfColumns},\asexp{numberOfRows}}
#endif
	map:		(R -> R) -> V R -> %;
	map:		(R -> R) -> % -> %;
	map!:		(R -> R) -> % -> %;
#if ALDOC
\aspage{map}
\astarget{\name!}
\Usage{\name~f\\\name!~f\\ \name(f)([$v_1,\dots,v_n$])\\
\name(f)(A)\\\name!(f)(A)}
\Signatures{
\name: (R $\to$ R) $\to$ \astype{Vector} R $\to$ \%\\
\name: (R $\to$ R) $\to$ \% $\to$ \%\\
\name!: (R $\to$ R) $\to$ \% $\to$ \%\\
}
\Params{
{\em f} & R $\to$ R & a map\\
{$v_i$} & R & Entries of a vector\\
{\em A} & \% & A matrix\\
}
\Descr{ \name(f)([$v_1,\dots,v_n$]) returns the square matrix
$$
\pmatrix{
v_1    & \dots &   v_n  \cr
f(v_1) & \dots & f(v_n) \cr
\vdots &        & \vdots \cr
f^{n-1}(v_1) & \dots & f^{n-1}(v_n) \cr
}
$$
while \name(f)(A) returns $f(A)$,~\ie~$f$ applied to $A$ pointwise,
and \name(f) returns either the mapping $v \to f(v)$ or $A \to f(A)$.
For matrices, \name!~does not make a copy of $A$ but modifies it in place.
}
#endif
	numberOfColumns:	% -> I;
	numberOfRows:		% -> I;
#if ALDOC
\aspage    {numberOfColumns,numberOfRows}
\astarget  {numberOfColumns}
\astarget  {numberOfRows}
\Usage     {numberOfColumns~A\\ numberOfRows~A}
\Signature {\%}{\astype{MachineInteger}}
\Params    {{\em A} & \% & A matrix\\}
\Retval    {The number of columns (resp.~rows) in {\em A}.}
\seealso   {\asexp{dimensions}}
#endif
	one:           I -> %;
	one?:		% -> Boolean;
#if ALDOC
\aspage    {one,one?}
\astarget{one}
\astarget{one?}
\Usage     {one~n\\ one?~A}
\Signatures{
one:  & \astype{MachineInteger} $\to$ \%\\
one?: & \% $\to$ \astype{Boolean}\\
}
\Params{
{\em n} & \astype{MachineInteger} & an integer\\
{\em A} & \% & A matrix\\
}
\Descr{one(n) returns an $n$ by $n$ identity matrix, while one?(A)
returns \true if {\em A} is an identity matrix, \false otherwise.}
\seealso{\asexp{square?},\asexp{zero},\asexp{zero?}}
#endif
	if R has Ring then {
		random: () -> %;
		random: (I,I) -> %;
#if ALDOC
\aspage    {random}
\Usage     {\name()\\ \name(n,m)}
\Signatures{
\name: & () $\to$ \%\\
\name: & (\astype{MachineInteger}, \astype{MachineInteger}) $\to$ \%\\
}
\Params{{\em n,m} & \astype{MachineInteger} & The dimensions of the new matrix.}
\Retval    {\name() returns a random matrix with random size, while
\name(n, m) returns a random matrix with n rows and m columns.}
#endif
	}
	set!:          (%,I,I,R) -> R;
#if ALDOC
\aspage{set!}
\Usage{\name(A, n, m, x)\\ A(n,m) := x}
\Signature{(\%,\astype{MachineInteger},\astype{MachineInteger},R)}{R}
\Params{
{\em A} & \% & A matrix\\
{\em n, m} & \astype{MachineInteger} & Indices\\
{\em c} & R & An entry\\
}
\Descr{Sets $A(n,m)$ to $c$ and returns $c$.}
#endif
	setMatrix!:	(%,I,I,%) -> %;
#if ALDOC
\aspage{setMatrix!}
\Usage{\name(A, n, m, B)}
\Signature{(\%,\astype{MachineInteger},\astype{MachineInteger},\%)}{\%}
\Params{
{\em A, B} & \% & Matrices\\
{\em n, m} & \astype{MachineInteger} & Indices\\
}
\Descr{Inserts $B$ as a submatrix of $A$ starting at
$A(n,m)$ and returns $B$.}
#endif
	square?: % -> Boolean;
#if ALDOC
\aspage{square?}
\Usage{\name~A}
\Signature{\%}{\astype{Boolean}}
\Params{ {\em A} & \% & A matrix\\ }
\Retval{Returns \true if $A$ is a square matrix, \false otherwise.}
\seealso{\asexp{diagonal?},\asexp{one?}}
#endif
	tensor: (%, %) -> %;
#if ALDOC
\aspage{tensor}
\Usage{\name(A,B)}
\Signature{(\%,\%)}{\%}
\Params{ {\em A, B} & \% & Matrices\\ }
\Retval{Returns $A \otimes B$, \ie~the matrix satisfying
$(A \otimes B) (u \otimes v) = A u \otimes B v$ for all vectors $u,v$.}
#endif
	transpose:	V R -> %;
	transpose:	% -> %;
	transpose!:	% -> %;
#if ALDOC
\aspage    {transpose}
\astarget{\name!}
\Usage     {\name~v\\ \name~A\\ \name!~A}
\Signatures{
\name: & \astype{Vector} R $\to$ \%\\
\name,\name!: & \% $\to$ \%\\
}
\Params{
{\em v} & \astype{Vector} R & A vector\\
{\em A} & \% & A matrix\\
}
\Retval{Return the transpose of $v$ (resp.~$A$).}
\Remarks{\name!~does not make a copy of $A$, which is therefore
replaced by its transpose. It is only applicable to square matrices.}
#endif
	if R has DifferentialRing then {
		wronskian: V R -> %;
#if ALDOC
\aspage{wronskian}
\Usage{\name~[$v_1,\dots,v_n$]}
\Signature{\astype{Vector} R}{\%}
\Params{ {$v_i$} & R & Entries of a vector\\ }
\Descr{ \name([$v_1,\dots,v_n$]) returns the square matrix
$$
\pmatrix{
v_1  & \dots & v_n  \cr
v_1' & \dots & v_n' \cr
\vdots &        & \vdots \cr
v_1^{(n-1)} & \dots & v_n^{(n-1)} \cr
}
$$
}
#endif
}
	zero:           (I, I) -> %;
	zero!:		% -> ();
	zero?:		% -> Boolean;
#if ALDOC
\aspage{zero}
\astarget{\name!}
\astarget{\name?}
\Usage     {\name(n,m)\\ \name!~A\\ \name?~A}
\Signatures{
\name:  & (\astype{MachineInteger}, \astype{MachineInteger}) $\to$ \%\\
\name!: & \% $\to$ ()\\
\name?: & \% $\to$ \astype{Boolean}\\
}
\Params{
{\em n,m} & \astype{MachineInteger} & integers\\
{\em A} & \% & A matrix\\
}
\Descr{\name(n,m) returns an $n$ by $m$ zero matrix, while
\name!(A) fills $A$ with $0$'s and \name?(A)
returns \true if all the entries of {\em A} are $0$, \false otherwise.}
\seealso{\asexp{one},\asexp{one?}}
#endif

#if NOMOREBLOODYCOMPILERBUGS
	default {
	copy:% -> %		== map((r:R):R +-> r);
	-: % -> %		== map((r:R):R +-> -r);
	minus!: % -> %		== map!((r:R):R +-> -r);
	map(f:R -> R):% -> %	== (a:%):% +-> map!(f)(copy a);
	colSwap!(a:%,i:I,j:I):%	== colSwap!(a,i,j,1,numberOfRows a);
	rowSwap!(a:%,i:I,j:I):%	== rowSwap!(a,i,j,1,numberOfColumns a);
	numberOfRows(a:%):I	== { (r,c) := dimensions a; r; }
	numberOfColumns(a:%):I	== { (r,c) := dimensions a; c; }
	tensor(a:%, b:%):%	== transpose [tensorGen(a, b)];
	(a:%)^(n:I):%		== { import from Integer; a^(n::Integer); }

	colCombine! (a:%,c1:R,i1:I,c2:R,i2:I) : % ==
		colCombine! (a,c1,i1,c2,i2,1,numberOfRows a);

	colCombine! (a:%,c1:R,i1:I,c2:R,i2:I,j1:I,j2:I) : % ==
		colCombine! (a,(x:R,y:R):R +-> c1*x+c2*y, i1,i2,j1,j2);

	colCombine! (a:%,f:(R,R)->R,i1:I,i2:I) : % ==
		colCombine! (a,f,i1,i2,1,numberOfRows a);

	rowCombine! (a:%,c1:R,i1:I,c2:R,i2:I) : % ==
		rowCombine! (a,c1,i1,c2,i2,1,numberOfColumns a);

	rowCombine! (a:%,c1:R,i1:I,c2:R,i2:I,j1:I,j2:I) : % ==
		rowCombine! (a,(x:R,y:R):R +-> c1*x+c2*y, i1,i2,j1,j2);

	rowCombine! (a:%,f:(R,R)->R,i1:I,i2:I) : % ==
		rowCombine! (a,f,i1,i2,1,numberOfColumns a);

	map(f:R -> R)(v:V R):% == {
		n := #v;
		a := zero(n, n);
		for j in 1..n repeat a(1,j) := v.j;
		for i in 2..n repeat for j in 1..n repeat
			a(i, j) := f a(prev i, j);
		a;
	}

	square?(a:%):Boolean == {
		import from I;
		(n, m) := dimensions a;
		n = m;
	}

	column(a:%, j:I):V R == {
		(n, m) := dimensions a;
		assert(j > 0); assert(j <= m);
		[a(i, j) for i in 1..n];
	}

	row(a:%, i:I):V R == {
		(n, m) := dimensions a;
		assert(i > 0); assert(i <= n);
		[a(i, j) for j in 1..m];
	}

	columns(a:%):Generator V R == generate {
		import from I;
		n := numberOfColumns a;
		for i in 1..n repeat yield column(a, i);
	}

	rows(a:%):Generator V R == generate {
		import from I;
		n := numberOfRows a;
		for i in 1..n repeat yield row(a, i);
	}

	(a:%) ^ (n:Integer):% == {
		assert(n >= 0);
		assert(square? a);
		zero? n => one numberOfRows a;
		one? n => a;
		b := copy a;
		for i in 2..n repeat b := times!(b, a);
		b;
	}

	(c:R) * (a:%):% == {
		zero? c => zero dimensions a;
		one? c => a;
		c = -1 => -a;
		map((r:R):R +-> c * r)(a);
	}

	times!(c:R, a:%):% == {
		zero? c => map!((r:R):R +-> 0)(a);
		one? c => a;
		c = -1 => minus! a;
		map((r:R):R +-> c * r)(a);
	}

	one (n:I): % == {
		import from R;
		assert(n>0);
		o := zero(n,n);
		for i in 1..n repeat o(i,i) := 1@R;
		o;
	}

	companion (l:V R, a:R == 1):% == {
		import from I, R;
		n := #l;
		assert(n>0);
		o := zero(n,n);
		for i in 1..prev n repeat {
			o(i,n) := l.i;
			o(next i, i) := a;
		}
		o(n, n) := l.n;
		o;
	}

	diagonal (l:V R): % == {
		import from I;
		n := #l;
		assert(n>0);
		o := zero(n,n);
		for i in 1..n repeat o(i,i) := l.i;
		o;
	}

	one?(a:%):Boolean == {
		import from I, R;
		~diagonal?(a) => return false;
		n := numberOfRows a;
		for i in 1..n repeat ~one?(a(i,i)) => return false;
		true;
	}

	extree (a:%) : ExpressionTree == {
		import from I, R, V R, List ExpressionTree;
		(r, c) := dimensions a;
		l := [extree r, extree c];
		for v in rows a repeat l := append!(l, [extree x for x in v]);
		ExpressionTreeMatrix l;	
	}

	local tensorGen(a:%, b:%):Generator V R == generate {
		import from V R;
		for u in rows a repeat for v in rows b repeat yield tensor(u,v);
	}

	if R has DifferentialRing then {
		wronskian(v:V R):% == {
			import from R;
			map(differentiate) v;
		}
	}

	if R has Ring then {
		random():% == {
			import from I;
			random(1+random()$I mod 100, 1+random()$I mod 100);
		}
	}
	}
#endif
}
