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
------------------------   linalgID.as   -----------------------
#include "sumit.as"

#if ASDOC
\thistype{LinearAlgebraOverIntegralDomain}
\History{Marco Codutti}{12 May 95}{created}
\Usage{import from \this(R,M)}
\Params{
{\em R} & IntegralDomain & A coefficient ring\\
{\em M} & MatrixCategory0 R & A matrix type over R\\
}
\Descr{\this(R, M) provides an implementation of various linear algebra
functions for coefficients belonging to an integral domain.
Algorithms do not use gcd, remainder or field division.}
\begin{exports}
nullSpace: & M $\to$ List V & nullspace basis of a matrix\\
rank: & M $\to$ SI & rank of a matrix\\
\end{exports}
\Aswhere{
SI &==& SingleInteger\\
V  &==& Vector R\\
}
#endif

macro SI  == SingleInteger;
macro ARR == PrimitiveArray SI;
macro V   == Vector R;
import from SI,ARR;

LinearAlgebraOverIntegralDomain(R: IntegralDomain, P:MatrixCategory0 R): 
with {
          nullSpace:     P -> List V;
#if ASDOC
\aspage	 {nullSpace}
\Usage	 {\name~A}
\Signature {P}{List Vector R}
\Params    {{\em A} & M & A matrix with coefficients from R.}
\Descr	 {Compute a basis for the nullspace of {\em A}.}
\Remarks{
          The base vectors may be non minimal, i.e. the gcd of the elements
          of a vector may be different from 1. 
          It happens because no gcd is used in the algorithm. 
          This will only occur when the elements of $A$ have some symmetries.
}
#endif
		rank:	P -> SI;
#if ASDOC
\aspage	 {rank}
\Usage	 {\name~A}
\Signature {P}{SI}
\Params    {{\em A} & M & A matrix with coefficients from R.}
\Retval	 {the rank of {\em A}}
#endif

} == add {

	import from R;

#if (ASDOC)
\aspage	 {GaussianElimination!}
\Usage	 {\name~A}
\Signature {M}{(SI,R,PrimitiveArray SI)}
\Params    {{\em A} & M & A matrix with coefficients from R.}
\Descr	 {
     Perform an in-place partial Gaussian Elimination on $A$.
     }
\Retval    {
     $(r,d,p)$ where $r$ is the rank of $A$, $d$ is its determinant and
     $p$ is a permutation on the columns of $A$. Columns $p_1$ to $p_r$
     of $A$ are linearly independant.  
     }
\Remarks{
     After this process, matrix $A$ has that form (provided that the
     columns permutation defined by $p$ is applied)
     \[
          A = \left( \begin{array}{cc}
          T &  A_1 \\
          0 &  A_2 \\
          \end{array} \right)
     \]
     where $T$ is an $(r \times r)$ upper triangular matrix with 
     $T_{rr} = \pm d$.
     \\
     Reference: Geddes, Czapor and Labahn, 
     {\em Algorithms for computer algebra}.
}
#endif
	GaussianElimination! (a:P) : (SI,R,ARR) ==
	{	
	    import from Partial R;
	    import from List SI;

	    local {
		(m,n)       := dimensions a;
		divisor: R  := 1;
		sign   : R  := 1;
		r      : SI := 1;
		p      : SI := 0; -- !!! (Warning) si on assigne pas
		k      : SI := 0; -- idem
		c      : PrimitiveArray SI := new(n,0);
		rang   : SI     := 0;
		dep    : SI     := n+1;
	    }

	    TRACE("--> GaussianElimination","");

	    for free(k) in 1..n while r<=m repeat
	    {
		for free(p) in r..m while a(p,k)=0 repeat {}
		if a(p,k)~=0 then
		{
TRACE("matrix : ",a);
TRACE("k = ", k);
TRACE("p = ", p);
TRACE("r = ", r);
TRACE("divisor = ", divisor);
		    rang := rang+1; c.rang := k;
		    if (p>r) then
		    {
			sign := -sign;
			rowSwap! (a,p,r,k,n);
TRACE("After swap: ", a);
		    }
		    ark := a(r,k);
TRACE("pivot : ", ark );
		    for i in r+1..m repeat
		    {
TRACE("combining with row: ", i);
			aik := a(i,k);
			rowCombine! (a, (x:R,y:R):R +-> quotient(ark*x-aik*y,divisor),
                              i,r, k+1,n);
			a(i,k) := 0;
		    }
		    divisor := ark;
		    r       := r+1;
		}
		else
          {
			dep := dep-1; c.dep := k;
		}
	    }
	    if r=m+1 then det := sign*divisor; else det := 0;
	    if r<=m then k := k+1;
	    for j in k..n repeat
	    {
		dep := dep-1;
		c.dep := j;
	    }
	    TRACE( "Result = ", a );
	    TRACE( "Rank = ", rang );
	    TRACE( "Det = ", det );
	    TRACE( "Columns permutation = ", [c.i for i in 1..n] );
	    
	    (rang,det,c);
	}

#if (ASDOC)
\aspage	 {fullGaussian!}
\Usage	 {\name~(A,r)}
\Signature {(M,SI)}{M}
\Params    {{\em A} & M & A matrix with coefficients from R.\\
            {\em r} & SI & the rank of $A$.}
\Descr	 {
     Continue the work of {\bf GaussianElimination!} by performing a
     full in-place Gaussian elimination.
     Matrix $A$ must be the result of {\bf GaussianElimination!}.
     }
\Retval    {
     a matrix having the form described below.
     }
\Remarks{
     After this process, matrix $A$ has that form (provided that the
     columns permutation defined by $p$, cf {\bf GaussianElimination!},
     is applied)
     \[
          A = \left( \begin{array}{cc}
          d*1 &  A_1 \\
          0   &  A_2 \\
          \end{array} \right)
     \]
     where $d$ is the determinant of the original matrix.
     \\
     Reference: Geddes, Czapor and Labahn, 
     {\em Algorithms for computer algebra}.
}
#endif

	fullGaussian! (a:P,rang:SI) : P ==
	{
	    import from Partial R;

	    TRACE ( "-->full Gaussian", "" ); 
	    div:R  := 1;
	    k  :SI := 1;
	    for r in 1..rang repeat
	    {
		while a(r,k)=0 repeat k:=k+1;
		ark := a(r,k);
		for i in 1..r-1 repeat
		{
		    aik := a(i,k);
		    rowCombine! (a, (x:R,y:R):R +-> 
				retract exactQuotient(ark*x-aik*y,div), i,r);
		}
		div := ark;
	    }
	    TRACE("a = ", a );
	    a;
	}

	rank (a:P) : SI == {
		-- (n,m)   := dimensions a;
		(r,d,c) := GaussianElimination! copy a;
		r;
	}

     nullSpace (a:P) : List V ==
     {
		import from Partial R;

		TRACE ("--> nullSpace", "" );

		b         := copy a;
		(n,m)     := dimensions a;
		(r,det,c) := GaussianElimination! b;
		d         := m-r;

		d = 0 => empty();
		r = 0 => { -- the unit matrix forms a basis
			basis:List V := empty();
			for i in 1..m repeat
			{
				null    := zero(m)$V;
				null(i) := 1;
				basis   := cons(null,basis);
			}
			return basis;
		};

		det          := b(r,c(r));
		b            := fullGaussian!(b,r);
		basis:List V := empty();

		TRACE ("nullSpace dim : ", d );

		for l in 1..d repeat
		{
			cl := c(r+l);
			null:V   := zero(m)$V;
			null(cl) := -det;
			for k in 1..r repeat null(c(k)) := b(k,cl);
			basis := cons(null,basis);
		}
		basis;
     }
}
