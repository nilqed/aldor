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
------------------------   matcat0.as   -----------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1995-1998
-- Copyright INRIA, 1998

#include "sumit"

#if ASDOC
\thistype{MatrixCategory0}
\History{Marco Codutti}{12 may 95}{created}
\Usage{\this~R: Category}
\Params{ {\em R} & SumitRing & The coefficient ring of the matrices\\ }
\Descr{\this~is a common category for matrices with coefficients in an arbitrary ring R.}
\begin{exports}
\category{SumitType}\\
$*$: & (\%,\%) $\to$ \% & multiplication\\
$*$: & (R,\%) $\to$ \% & left multiplication by a scalar\\
$*$: & (\%,R) $\to$ \% & right multiplication by a scalar\\
$*$: & (\%,V) $\to$ V & multiplication by a vector\\
$+$: & (\%,\%) $\to$ \% & addition\\
$-$: & (\%,\%) $\to$ \% & substraction \\
$-$: & \% $\to$ \% & additive inverse of a matrix\\
$\hat{}$: & (\%,SI) $\to$ \% & exponentiation\\
add!: & (\%,\%) $\to$ \% & in-place addition\\
apply: & (\%,SI,SI) $\to$ R & extract an entry from the matrix\\
apply: & (\%,SI,SI,SI,SI) $\to$ \% & extract a submatrix\\
coerce: & V $\to$ \% & coerce a vector to a one-column matrix\\
colCombine!: & (\%,R,SI,R,SI,SI,SI) $\to$ \% & In-place linear combination of columns\\ 
colCombine!: &(\%,FR,SI,SI,SI,SI) $\to$ \% & In-place combination of columns\\ 
cols: & \% $\to$ SI & return the number of columns of the matrix\\
colSwap!: & (\%,SI,SI,SI,SI) $to$ \% & In-place columns swaping\\
column: & (\%,SI) $\to$ V & extraction of a column\\
copy: & \% $\to$ \% & copy a matrix\\
diagonal: & List R $\to$ \% & creates a diagonal matrix\\
diagonal?: & \% $\to$ Boolean & test for a diagonal matrix\\
dimensions: & \% $\to$  (SI,SI) & get row and column dimensions\\
map!: & (R $\to$ R,\%) $\to$ \% & apply a function to each entry\\
minus!: & \% $\to$ \% & in-place additive inverse\\
one: & SI $\to$ \% & create a diagonal matrix with ones on the diagonal\\
one?: & \% $\to$ Boolean & test for a one-matrix\\
random: & (SI,SI) $\to$ \% & create a random matrix\\
row: & (\%,SI) $\to$ V & extraction of a row\\
rowCombine!: & (\%,R,SI,R,SI,SI,SI) $\to$ \% & In-place linear combination of rows\\ 
rowCombine!: & (\%,FR,SI,SI,SI,SI) $\to$ \% & In-place combination of rows\\ 
rows: & \% $\to$ SI & return the number of rows of the matrix\\
rowSwap!: & (\%,SI,SI,SI,SI) $to$ \% & In-place rows swaping\\
set!: & (\%,SI,SI,R) $\to$ R & set an entry in the matrix\\
set!: & (\%,SI,SI,\%) $\to$ \% & modify a submatrix of a matrix\\
substract!: & (\%,\%) $\to$ \% & in-place substraction\\
tensor: & (\%, \%) $\to$ \% & tensor product\\
times!: & (R,\%) $\to$ \% & in-place left multiplication by a ring element\\
times!: & (\%,R) $\to$ \% & in-place right multiplication by a ring element\\
transpose: & \% $\to$ \% & transpose the matrix\\
zero: & (SI,SI) $\to$ \% & create a zero matrix\\
zero?: & \% $\to$ Boolean & test if all entries are zero\\
\end{exports}
\begin{exports}[if R has IntegralDomain]
determinant: & \% $\to$ R & determinant\\
nullSpace: & \% $\to$ List V  & basis of the nullspace\\
rank: & \% $\to$ SI & rank of a matrix\\
span: & \% $\to$ (SI, PrimitiveArray SI) & span of a matrix\\
\end{exports}
\Aswhere{
SI &==& SingleInteger\\
V  &==& Vector R\\
FR &==& (R,R)$\to$R\\
}
#endif

macro SI == SingleInteger;
macro V == Vector R;
import from SI;

MatrixCategory0(R: SumitRing): Category == SumitType with {
	*:              (%,%) -> %;
	*:              (R,%) -> %;
	*:              (%,R) -> %;
	*:              (%,V) -> V;
#if ASDOC
\aspage{$*$}
\begin{usage}
c~\name~A\\
A~\name~c\\
A~\name~B\\
A~\name~v\\
\end{usage}
\Signatures{
\name: & (\%,\%) $\to$ \%\\
\name: & (R,\%) $\to$ \%\\
\name: & (\%,R) $\to$ \%\\
\name: & (\%,Vector R) $\to$ Vector R
}
\Params{
{\em c} & R & An element of the coefficient ring.\\
{\em A},{\em B} & \% & Matrices with coefficients from R.\\
{\em v} & Vector R & a vector with coefficients from R.
}
\Descr 
{Multiplication of a matrix by a scalar, an other matrix or a vector.}
\seealso {times!(\this)}
#endif
	+:              (%,%) -> %;
#if ASDOC
\aspage    {+}
\Usage     {A~\name~B}
\Signature {\%}{\%}
\Params    {{\em A},{\em B} & \% & Matrices with coefficients from R.}
\Descr     {Addition of two matrices.}
\seealso   {add!(\this)}
#endif
	-:              (%,%) -> %;
#if ASDOC
\aspage    {-}
\Usage     {A~\name~B}
\Signature {(\%,\%)}{\%}
\Params    {{\em A},{\em B} & \% & Matrices with coefficients from R.}
\Descr     {subtraction of two matrices.}
\seealso   {subtract!(\this)}
#endif
	-:              % -> %;
#if ASDOC
\aspage    {-}
\Usage     {\name~A}
\Signature {\%}{\%}
\Params    {{\em A} & \% & A matrices with coefficients from R.}
\Descr     {Additive inverse of a matrix.}
#endif
	^:              (%,SI) -> %;
#if ASDOC
\aspage    {$\hat{}$}
\Usage     {A~\name~n}
\Signature {(\%,SI)}{\%}
\Params{
{\em A} & \% & A Matrix with coefficients from R.\\
{\em n} & SI & The integer exponent.\\
}
\Descr {Exponentiation of a matrix by an integer.}
#endif
	add!:		(%,%) -> %;
#if ASDOC
\aspage    {add!}
\Usage     {\name(A,B)}
\Signature {(\%,\%)}{\%}
\Params    {{\em A},{\em B} & \% & Matrices with coefficients from R.}
\Descr     {In-place addition of two matrices. {\em A} is altered.}
#endif
	apply:          (%,SI,SI) -> R;
	apply:          (%,SI,SI,SI,SI) -> %;
#if ASDOC
\aspage{apply}
\begin{usage}
\name(A,n,m)\\
\name(A,n,m,r,c)
\end{usage}
\Signatures{
\name: & (\%,SI,SI) $\to$ R\\
\name: & (\%,SI,SI,SI,SI) $\to$ \%\\
}
\Params{
{\em A} & \% & A matrix with coefficients from R.\\
{\em n,m,r,c} & SI & integers.\\
}
\begin{descr}
Either returns the $(n,m)$ element of {\em A} or the submatrix starting at $(n,m)$ with
$r$ rows and $c$ columns.
\end{descr}
#endif
     coerce:         V -> %;
#if ASDOC
\aspage    {coerce}
\Usage     {\name~v}
\Signature {Vector R}{\%}
\Params{
{\em v} & Vector R & a vector.\\
}
\Descr {coerce vector $v$ to a one-column matrix.}
#endif
	colCombine!:	 (%,R,SI,R,SI) -> %;
	colCombine!:	 (%,R,SI,R,SI,SI,SI) -> %;
	colCombine!:    (%,(R,R)->R,SI,SI) -> %;
	colCombine!:    (%,(R,R)->R,SI,SI,SI,SI) -> %;
#if ASDOC
\aspage	{colCombine!}
\Usage    {\name (A,f,j1,j2,i1,i2) \\
	     \name (A,c1,j1,c2,j2,i1,i2)}
\Signatures {(\%,(R,R) $\to$ R,SI,SI,SI,SI) $\to$ \% \\
	     (\%,R,SI,R,SI,SI,SI) $\to$ \%}
\Params   {{\em A} & \% & A matrix with coefficients from R \\
	     {\em f} & (R,R) $\to$ R & An operation between two elements from R\\
	     {\em c1}, {\em c2} & R & elements from R \\
	     {\em j1}, {\em j2} & SI & columns of {\em A} \\
	     {\em i1}, {\em i2} & SI & rows of {\em A} }
\Descr	{column $j1$ of $A$ is replaced by a combination of
	    columns $j1$ and $j2$.
	    This operation is applied only for rows $i1$ (default 1)
	    to $i2$ (default rows $A$). That is,
	    \[
		A_{ij_1} \leftarrow f(A_{ij_1},A_{ij_2}) 
		\quad i=i_1,\ldots,i_2
	    \]
	    The second form is equivalent to the first one with function $f$
	    defined by $f: (x,y) \to  c_1\,x+c_2\,y$.
           }
#endif
	cols:		% -> SI;
#if ASDOC
\aspage    {cols}
\Usage     {\name~A}
\Signature {\%}{SI}
\Params    {{\em A} & \% & A matrix with coefficients from R.}
\Retval    {The number of columns in {\em A}.}
\seealso   {rows(\this), dimensions(\this)}
#endif
	colSwap!:	(%,SI,SI) -> %;
	colSwap!:	(%,SI,SI,SI,SI) -> %;
#if ASDOC
\aspage    {colSwap!}
\Usage     {\name (A,j1,j2,i1,i2)}
\Signature {(\%,SI,SI,SI,SI)}{\%}
\Params    {{\em A} & \% & A matrix with coefficients from R \\
	      {\em j1}, {\em j2} & SI & columns of {\em A} \\
	      {\em i1}, {\em i2} & SI & rows of {\em A} }
\Descr     {In-place swaping of columns $j1$ and $j2$ of matrix $A$.
	      This operation is applied only for rows $i1$ (default 1)
	      to $i2$ (default rows $A$)
	      }
#endif
	column: (%, SI) -> V;
#if ASDOC
\aspage{column}
\Usage{\name~A}
\Signature{(\%,SingleInteger)}{Vector R}
\Params{
{\em A} & \% & A matrix with coefficients from R \\
{\em c} & SingleInteger & A column index\\
}
\Retval{Returns the $\sth{c}$ column of A as a vector.}
\seealso{row(\this)}
#endif
	copy:		% -> %;
#if ASDOC
\aspage    {copy}
\Usage     {\name~A}
\Signature {\%}{\%}
\Params    {{\em A} & \% & A matrix with coefficients from R.}
\Retval    {A copy of matrix {\em A}.}
#endif
	diagonal:	List R -> %;
#if ASDOC
\aspage    {diagonal}
\Usage     {\name~L}
\Signature {List R}{\%}
\Params    {{\em L} & List R & A list with the diagonal coefficients.}
\Descr     {Creates a diagonal matrix whose elements are given by {\em L}.}
#endif
	diagonal?:	% -> Boolean;
#if ASDOC
\aspage    {diagonal?}
\Usage     {\name~A}
\Signature {\%}{Boolean}
\Params    {{\em A} & \% & A matrix with coefficients from R.}
\Descr     {Test if {\em A} is a diagonal matrix.}
#endif
	dimensions:     % -> (SI,SI);
#if ASDOC
\aspage    {dimensions}
\Usage     {\name~A}
\Signature {\%}{(SI,SI)}
\Params    {{\em A} & \% & A matrix with coefficients from R.}
\Retval    {The number of rows and columns in {\em A}}
\seealso   {cols(\this), rows(\this)}
#endif
	map!:		(R -> R,%) -> %;
#if ASDOC
\aspage    {map!}
\Usage     {\name(f,A)}
\Signature {(R $\to$ R,\%)}{\%}
\Params{   {\em A} & \% & A matrix with coefficients from R.\\
           {\em f} & R $\to$ R & Any mapping from R to R.\\ }
\Descr     {Maps the function {\em f} onto each entry of {\em A}}
#endif
     minus!:        % -> %;
#if ASDOC
\aspage    {minus!}
\Usage     {\name~A}
\Signature {\%}{\%}
\Params    {{\em A} & \% & A matrices with coefficients from R.}
\Descr     {in-place additive inverse of a matrix.}
#endif
	one:           (SI) -> %;
#if ASDOC
\aspage    {one}
\Usage     {\name~n}
\Signature {SI}{\%}
\Params    {{\em n} & SI & an integer.}
\Descr     {Create an {\em n} by {\em n} one-matrix.}
#endif
	one?:		% -> Boolean;
#if ASDOC
\aspage    {one?}
\Usage     {\name~A}
\Signature {\%}{Boolean}
\Params    {{\em A} & \% & A matrix with coefficients from R.}
\Descr     {Test if {\em A} is the unit matrix.}
#endif
	random:		(SI,SI) -> %;
#if ASDOC
\aspage    {random}
\Usage     {\name(n,m)}
\Signature {(SI,SI)}{\%}
\Params    {{\em n},{\em m} & SI & Integers.}
\Descr     {Create a  {\em n} by {\em m} matrix with random entries.}
#endif
	row: (%, SI) -> V;
#if ASDOC
\aspage{row}
\Usage{\name~A}
\Signature{(\%,SingleInteger)}{Vector R}
\Params{
{\em A} & \% & A matrix with coefficients from R \\
{\em r} & SingleInteger & A row index\\
}
\Retval{Returns the $\sth{r}$ row of A as a vector.}
\seealso{column(\this)}
#endif
	rowCombine!:	(%,R,SI,R,SI) -> %;
	rowCombine!:	(%,R,SI,R,SI,SI,SI) -> %;
	rowCombine!:	(%,(R,R)->R,SI,SI) -> %;
	rowCombine!:	(%,(R,R)->R,SI,SI,SI,SI) -> %;
#if ASDOC
\aspage	   {rowCombine!}
\Usage     {\name (A,f,i1,i2,j1,j2) \\
	    \name (A,c1,i1,c2,i2,j1,j2)}
\Signatures {(\%,(R,R) $\to$ R,SI,SI,SI,SI) $\to$ \% \\
	     (\%,R,SI,R,SI,SI,SI) $\to$ \%}
\Params    {{\em A} & \% & A matrix with coefficients from R \\
	    {\em f} & (R,R) $\to$ R & An operation between two elements from R\\
	    {\em c1}, {\em c2} & R & elements from R \\
	    {\em i1}, {\em i2} & SI & rows of {\em A} \\
	    {\em j1}, {\em j2} & SI & columns of {\em A}}
\Descr	   {row $i1$ of $A$ is replaced by a combination of
	    rows $i1$ and $i2$.
	    This operation is applied only for columns $j1$ (default 1)
	    to $j2$ (default columns $A$). That is,
	    \[
		A_{i_1j} \leftarrow f(A_{i_1j},A_{i_2j})
		\quad j=j_1,\ldots,j_2
	    \]
	    The second form is equivalent to the first one with function $f$
	    defined by $f: (x,y) \to  c_1\,x+c_2\,y$.
           }
#endif
	rowSwap!:	(%,SI,SI) -> %;
	rowSwap!:	(%,SI,SI,SI,SI) -> %;
#if ASDOC
\aspage    {rowSwap!}
\Usage	 {\name (A,i1,i2,j1,j2)}
\Signature {(\%,SI,SI,SI,SI)}{\%}
\Params    {{\em A} & \% & A matrix with coefficients from R \\
	       {\em i1}, {\em i2} & SI & rows of {\em A} \\
	       {\em j1}, {\em j2} & SI & columns of {\em A} }
\Descr     {In-place swaping of rows $i1$ and $i2$ of matrix $A$.
            If $j1$ and $j2$ are given (default 1 and cols $A$ respectively),
            it means that we may restrict the swap to columns $j1$ to $j2$.
            Elements in the other columns are known to be the same in
            rows $i1$ and $i2$. This is just an indication. Implementation
            may decide to swap the entire lines anyway if it is more efficient
	      }
#endif
	rows:		% -> SI;
#if ASDOC
\aspage	   {rows}
\Usage     {\name~A}
\Signature {\%}{SI}
\Params    {{\em A} & \% & A matrix with coefficients from R.}
\Retval    {The number of rows in {\em A}.}
\seealso   {cols(\this), dimensions(\this)}
#endif
	set!:          (%,SI,SI,R) -> R;
	set!:		(%,SI,SI,%) -> %;
#if ASDOC
\aspage{set!}
\begin{usage}
\name(A,n,m,c)\\
\name(A,n,m,B)
\end{usage}
\Signatures{
\name: & (\%,SI,SI,R) $\to$ R\\
\name: & (\%,SI,SI,\%) $\to$ \%\\
}
\Params{
{\em A}, {\em B} & \% & Matrices\\
{\em n}, {\em m} & SI & Integers\\
{\em c} & R & An element from the coefficient ring\\
}
\begin{descr}
Set the $(n,m)$ element of {\em A} to {\em c}.\\
Insert the submatrix {\em B} into {\em A}, starting at
$(n,m)$.
\end{descr}
#endif
     substract!:    (%,%) -> %;
#if ASDOC
\aspage    {substract!}
\Usage     {\name~(A,B)}
\Signature {(\%,\%)}{\%}
\Params    {{\em A},{\em B} & \% & Matrices with coefficients from R.}
\Descr     {in-place subtraction of two matrices.}
#endif
	tensor: (%, %) -> %;
#if ASDOC
\aspage{tensor}
\Usage{\name(A,B)}
\Signature{(\%,\%)}{\%}
\Params{ {\em A}, {\em B} & \% & Matrices\\ }
\Retval{Returns $A \otimes B$, \ie~the matrix satisfying
$(A \otimes B) (u \otimes v) = A u \otimes B v$.}
#endif
	times!:		(R,%) -> %;
	times!:		(%,R) -> %;
#if ASDOC
\aspage     {times!}
\Usage      {\name(c,A) \\
	     \name(A,c) }
\Signatures {(R,\%) $\to$ \% \\
	     (\%,R) $\to$ \% }	
\Params{    {\em A} & \% & Matrices with coefficients from R.\\
            {\em c} & R & An element from the coefficient ring.}
\Descr	    {In-place left or right multiplication of a matrix by a scalar.}
#endif
	transpose:	% -> %;
#if ASDOC
\aspage    {transpose}
\Usage     {\name~A}
\Signature {\%}{\%}
\Params    {{\em A} & \% & A matrix with coefficients from R.}
\Retval    {the transpose of matrix {\em A}.}
#endif
	zero:		(SI,SI) -> %;
#if ASDOC
\aspage    {zero}
\Usage     {\name~n}
\Signature {SI}{\%}
\Params    {{\em n}, {\em m} & SI & Integers.}
\Descr     {Create an {\em n} by {\em m} matrix with zero coefficients.}
#endif
	zero?:		% -> Boolean;
#if ASDOC
\aspage    {zero?}
\Usage     {\name~A}
\Signature {\%}{Boolean}
\Params    {{\em A} & \% & A matrix with coefficients from R.}
\Descr     {Test if all the entries of {\em A} are zero.}
#endif

	if R has IntegralDomain then {
		determinant: % -> R;
#if ASDOC
\aspage{determinant}
\Usage	 {\name~A}
\Signature {\%}{R}
\Params    {{\em A} & \% & A matrix with coefficients from R.}
\Descr	 {Compute the determinant of A.}
#endif
		nullSpace:     % -> List V;
#if ASDOC
\aspage	 {nullSpace}
\Usage	 {\name~A}
\Signature {\%}{List Vector R}
\Params    {{\em A} & \% & A matrix with coefficients from R.}
\Descr	 {Compute a basis for the nullspace of {\em A}.}
\Remarks{
          The base vectors may be non minimal, i.e. the gcd of the elements
          of a vector may be different from 1. 
          It happens because no gcd is used in the algorithm. 
          This will only occur when the elements of $A$ have some symmetries.
}
#endif

		rank:	% -> SI;
#if ASDOC
\aspage    {rank}
\Usage     {\name~A}
\Signature {\%}{SI}
\Params    {{\em A} & \% & A matrix with coefficients from R.}
\Retval    {the rank of {\em A}}
#endif
		span: % -> (SI, PrimitiveArray SI);
#if ASDOC
\aspage{span}
\Usage{\name~A}
\Signature{\%}{(SingleInteger, PrimitiveArray SingleInteger)}
\Params{{\em A} & \% & A matrix with coefficients from R.}
\Retval{Returns $(r, [c_1,\dots,c_r])$ such that the columns
$c_1,\dots,c_r$ of $A$ form a basis of the span of $A$.}
#endif

	}

-- Default values for exported functions

default {

	import from R;

	(a:%) = (b:%) : Boolean == 
	{
		(n,m) := dimensions a;
		(n ~= rows(b)) or (m ~= cols(b)) => false;
		for i in 1..n repeat
			for j in 1..m repeat
				a(i,j) ~= b(i,j) => return false;
		true;
	}

	(port: TextWriter) << (a:%) : TextWriter ==
		tex(port,extree(a))$ExpressionTree;

	(c:R) * (a:%) : % == times!(c,copy a);
	(a:%) * (c:R) : % == times!(copy a,c);

	(a:%) * (b:%) : % == 
	{
		(na,ma) := dimensions(a);
		(nb,mb) := dimensions(b);
		ASSERT(ma=nb);
		r := zero(na,mb);
		for i in 1..na repeat
		    for j in 1..mb repeat {
			e:R := 0;
			for k in 1..ma repeat
				e := e + a(i,k) * b(k,j);
			r(i,j) := e;
		    }
		r;
	}			

     (a:%) * (v:V) : V ==
     {
          n := rows a;
          m := cols a;
          ASSERT(m=#v);
          r := zero(n)$V;
          for i in 1..n repeat
          {
               t := 0$R;
               for k in 1..m repeat t := t + a(i,k)*v(k);
               r(i) := t;
          }
          r;          
     }

	(a:%) ^ (e:SI) : % == 
	{
		ASSERT(rows(a)=cols(a));
		r:% := one(rows(a));
		for i in 1..e repeat r:=r*a;
		r;
	}

	(a:%) + (b:%) : % == add!( copy a, b );
	(a:%) - (b:%) : % == substract!( copy a, b );
           - (a:%) : % == minus! copy a;

	add! (a:%,b:%) : % == 
	{
		(n,m)   := dimensions(a);
		(nb,mb) := dimensions(b);
		ASSERT(n=nb);
		ASSERT(m=mb);
		for i in 1..n repeat {
			for j in 1..m repeat {
				a(i,j):=a(i,j)+b(i,j);
			}
		}
		a;
	}

	apply (a:%,i:SI,j:SI,n:SI,m:SI) : % == submatrix(a,i,j,n,m);

     coerce (v:V) : % ==
     {
          n := #v;
          a := zero(n,1);
          for i in 1..n repeat a(i,1) := v(i);
          a;
     }

	column(a:%, c:SI):V == {
		v:V := zero(r := rows a);
		for i in 1..r repeat v.i := a(i, c);
		v;
	}

	colCombine! (a:%,c1:R,i1:SI,c2:R,i2:SI) : % ==
		colCombine! (a,c1,i1,c2,i2,1,rows a);

	colCombine! (a:%,c1:R,i1:SI,c2:R,i2:SI,j1:SI,j2:SI) : % ==
		colCombine! (a,(x:R,y:R):R +-> c1*x+c2*y, i1,i2,j1,j2);

	colCombine! (a:%,f:(R,R)->R,i1:SI,i2:SI) : % ==
		colCombine! (a,f,i1,i2,1,rows a);

	colCombine! (a:%,f:(R,R)->R,i1:SI,i2:SI,j1:SI,j2:SI) : % ==
	{
		for j in j1..j2 repeat a(j,i1) := f(a(j,i1),a(j,i2));
		a;
	}

	colSwap! (a:%,i1:SI,i2:SI ): % == colSwap! (a,i1,i2,1,rows a);

	colSwap! (a:%,i1:SI,i2:SI,j1:SI,j2:SI ): % ==
	{
		for j in j1..j2 repeat
		{
			t := a(j,i1); a(j,i1) := a(j,i2); a(j,i2) := t;
		};
		a;
	}

	diagonal (l:List R): % ==
	{
		n := #l;
		ASSERT(n>0);
		o:% := zero(n,n);
		for i in 1.. for e in l repeat o(i,i) := e;
		o;
	}

	diagonal? (a:%) : Boolean == 
	{
		for i in 1..rows(a) repeat 
			for j in 1..cols(a) | (i~=j) repeat 
				a(i,j) ~= 0 => return false;
		true;
	}

	dimensions (a:%) : (SI,SI)    == (rows(a),cols(a));

	extree (a:%) : ExpressionTree == 
	{
	    import from List ExpressionTree;
            import from ExpressionTreeLeaf;
	    import from List R;

	    (n,m) := dimensions a;
         l     := empty()$List(ExpressionTree);
         for i in rows(a)..1 by -1 repeat
          for j in cols(a)..1 by -1 repeat
               l := cons(extree a(i,j),l);
	    ExpressionTreeMatrix concat! ( [extree leaf n,extree leaf m], l );
	}
	
	map! (op: R -> R,a:%) : % == 
	{
		(n,m) := dimensions a;
		for i in 1..n repeat 
			for j in 1..m repeat
				a(i,j) := op a(i,j);
		a;
	}

	minus!(a:%) : % == map!( (x:R):R +-> -x, a );

	one (n:SI) : % == 
	{
		o:% := zero(n,n);
		for i in 1..n repeat o(i,i) := 1;
		o;
	}

	one? (a:%) : Boolean == 
	{
		for i in 1..rows(a) repeat {
			for j in 1..cols(a) repeat {
				aij := a(i, j);
				if (i~=j) then ~(zero? aij) => return false;
				          else ~(one? aij) => return false;
			}
		}
		true;
	}

	row(a:%, r:SI):V == {
		v:V := zero(c := cols a);
		for j in 1..c repeat v.j := a(r, j);
		v;
	}

	rowCombine! (a:%,c1:R,i1:SI,c2:R,i2:SI) : % ==
		rowCombine! (a,c1,i1,c2,i2,1,cols a);

	rowCombine! (a:%,c1:R,i1:SI,c2:R,i2:SI,j1:SI,j2:SI) : % ==
		rowCombine! (a,(x:R,y:R):R +-> c1*x+c2*y, i1,i2,j1,j2);

	rowCombine! (a:%,f:(R,R)->R,i1:SI,i2:SI) : % ==
		rowCombine! (a,f,i1,i2,1,cols a);

	rowCombine! (a:%,f:(R,R)->R,i1:SI,i2:SI,j1:SI,j2:SI) : % ==
	{
		for j in j1..j2 repeat a(i1,j) := f(a(i1,j),a(i2,j));
		a;
	}

	rowSwap! (a:%,i1:SI,i2:SI ): % == rowSwap! (a,i1,i2,1,cols a);

	rowSwap! (a:%,i1:SI,i2:SI,j1:SI,j2:SI ): % ==
	{
		for j in j1..j2 repeat
		{
			t := a(i1,j); a(i1,j) := a(i2,j); a(i2,j) := t;
		}
		a;
	}
				
	sample : % == zero(1,1);
     
	set! (a:%,i:SI,j:SI,s:%) : % == 
	{
		(na,ma) := dimensions a;
		(ns,ms) := dimensions s;
		for k in 1..ns repeat {
			for l in 1..ms repeat {
				a(i+k-1,j+l-1) := s(k,l);
			}
		}
		s;
	}

	submatrix (a:%,r:SI,c:SI,n:SI,m:SI) : % == 
	{
		(an,am) := dimensions(a);
		b := zero(n,m);
		for i in 1..n repeat {
			for j in 1..m repeat {	
				b(i,j) := a(r+i-1,c+j-1);
			}
		}
		b;
	}

     substract! (a:%,b:%) : % == 
	{
		(n,m)   := dimensions(a);
		(nb,mb) := dimensions(b);
		ASSERT(n=nb);
		ASSERT(m=mb);
		for i in 1..n repeat {
			for j in 1..m repeat {
				a(i,j):=a(i,j)-b(i,j);
			}
		}
		a;
	}

	tensor(a:%, b:%):% == {
		(ra, ca) := dimensions a;
		(rb, cb) := dimensions b;
		u:V := zero ca;
		v:V := zero cb;
		r:SI := 1;
		rm := ra * rb;
		cm := ca * cb;
		m := zero(rm, cm);
		for i in 1..ra repeat {
			for k in 1..ca repeat u.k := a(i, k);
			for j in 1..rb repeat {
				for k in 1..cb repeat v.k := b(j, k);
				w := tensor(u, v);
				for k in 1..cm repeat m(r, k) := w.k;
				r := next r;
			}
		}
		m;
	}

	times! (c:R,a:%) : % == 
	{
		c=1 => a;
		(n,m) := dimensions(a);
		c=0 => zero(n,m);
		map!( (x:R):R +-> c*x, a );
	}

	times! (a:%,c:R) : % == 
	{
		c=1 => a;
		(n,m) := dimensions(a);
		c=0 => zero(n,m);
		map!( (x:R):R +-> x*c, a);
	}

	transpose (a:%) : % == 
	{
          b := zero(cols(a),rows(a));
		for i in 1..rows(a) repeat
			for j in 1..cols(a) repeat 
				b(j,i) := a(i,j);
		a;
	}

	zero?(a:%) : Boolean == 
	{
		for i in 1..rows(a) repeat
			for j in 1..cols(a) repeat
				a(i,j) ~= 0 => return false;
		true;
	}
}
}
