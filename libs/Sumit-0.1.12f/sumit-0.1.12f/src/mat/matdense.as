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
------------------------   matdense.as   -----------------------
#include "sumit"

#if ASDOC
\thistype{DenseMatrix}
\History {Laurent Bernardin}{23 Nov 1994}{created.}
\History {Marco Codutti}{10 May 1995}
	 {Updated for new releases of A\#, \sumit and {\em asdoc}.} 
\Usage   {import from \this~R}
\Params  {{\em R} & SumitRing & The coefficient ring of the matrices.}
\Descr   {\this~ is an implementation of dense mutable matrices.}
\begin{exports}
\category{MatrixCategory~R} \\
coerce: & \% $\to$ List R & return the elements of the matrix in a list \\
coerce: & \% $\to$ List List R & return the elements in a list of lists\\
matrix: & (SI,SI,List R) $\to$ \% & build a new matrix\\
matrix: & (List List R) $\to$ \% & build a new matrix\\
new: & (SI,SI,R) $\to$ \% & create a new matrix\\
\end{exports}
\Aswhere{
SI &==& SingleInteger\\
}
#endif

macro SI  == SingleInteger;
macro ARR == PrimitiveArray SI;

import from SI;
import from ARR;

DenseMatrix(R: SumitRing): MatrixCategory(R) with 
{
	coerce:		% -> List R;
	coerce:		% -> List List R;
#if ASDOC
\aspage     {coerce}
\Usage      {coerce~A}
\Signatures {\% $\to$ List R \\
	     \% $\to$ List List R }
\Params     {{\em A} & \% & A matrix with coefficients from R.}
\Retval	  {the elements of {\em A}, row by row, 
             as a list of lists or a flat list}
#endif
	matrix:		(SI,SI,List R) -> %;
	matrix:		List List R -> %;
#if ASDOC
\aspage     {matrix}
\Usage      {\name (n,m,l)\\
	     \name (ll)    }
\Signatures { (SI,SI,List R) $\to$ \% \\
	      List List R $\to$ \% }
\Params{    {\em n}, {\em m} & SI & dimensions of the matrix \\
            {\em l} & List R & a list containing the elements \\
	    {\em ll} & List List R & the elements row by row \\
	    }
\Descr{     Build a new matrix having {\em n} rows and {\em m} columns using
	    the elements in {\em l} or build a matrix with elements given by
	    {\em ll}.}
#endif
	new:		(SI,SI,R) -> %;
#if ASDOC
\aspage    {new}
\Usage     {\name(n,m,c)}
\Signature {(SI,SI,R)}{\%}
\Params{   {\em n},{\em m} & SI & Integers.\\
           {\em c} & R & An element from the coefficient ring.\\}
\Descr{    Create a new matrix with {\em n} rows and {\em m} columns.
	   All entries are initialized to {\em c}.}
#endif
}
== add
{
	DT  ==> PrimitiveArray R;
	Rep ==> Record(nbrows:SI,nbcolumns:SI,data:DT);

	import from R;
	import from Rep;

	(a:%) = (b:%) : Boolean == 
	{
		(n,m) := dimensions(a);
		(n ~= rows(b)) or (m ~= cols(b)) => false;
		aar := entries(a);
		abr := entries(b);
		for i in 1..n*m repeat aar.i ~= abr.i => return false;
		true;
	}


	(c:R) * (a:%) : % == 
	{
		c=1 => a;
		(n,m) := dimensions(a);
		c=0 => zero(n,m);
		aar := entries(a);
		rr:DT := new(n*m);
		for i in 1..n*m repeat rr.i := c * aar.i;
		matrix! (n,m,rr);
	}

	(a:%) * (c:R) : % == 
	{
		c=1 => a;
		(n,m) := dimensions(a);
		c=0 => zero(n,m);
		aar := entries(a);
		rr:DT := new(n*m);
		for i in 1..n*m repeat rr.i := aar.i*c;
		matrix! (n,m,rr);
	}

	(a:%) * (b:%) : % == 
	{
		(na,ma) := dimensions(a);
		(nb,mb) := dimensions(b);
		ASSERT(ma=nb);
		aar := entries(a);
		abr := entries(b);
		rr:DT := new(na*mb);
		ri:SI := 0;
		for i in 1..na for ai in 1.. by ma repeat {
		    for j in 1..mb repeat {
			e:R := 0;
			for aj in ai..ai+ma-1 for bj in j.. by mb repeat {
				e := e + aar.(aj) * abr.(bj);
			}
			ri := ri+1;
			rr.ri := e;
		    }
		}
		matrix! (na,mb,rr);
	}

	(a:%) + (b:%) : % == 
	{
		(n,m) := dimensions(a);
		ASSERT(n=rows(b));
		ASSERT(m=cols(b));
		aar := entries(a);
		abr := entries(b);
		rr:DT := new(n*m);
		for i in 1..n*m repeat rr.i := aar.i + abr.i;
		matrix! (n,m,rr);
	}

	- (a:%) : % == 
	{
		(n,m,ar) := elements(a);
		rr:DT := new(n*m);
		for i in 1..n*m repeat rr.i := -ar.i;
		matrix! (n,m,rr);
	}
	
	apply (a:%,i:SI,j:SI) : R == 
	{
		ASSERT(i>0);
		ASSERT(j>0);
		ASSERT(i<=rows(a));
		ASSERT(j<=cols(a));
		entries(a)(j+(i-1)*cols(a));
	}

	coerce (a:%) : List R == [ entries(a).i for i in 1..rows(a)*cols(a) ];
	coerce (a:%) : List List R == {
		(n,m,v) := elements a;
		l := empty()$(List List R);
		for i in 1..n for k in 1.. by m repeat
			cons( [v.j for j in k..k+m-1], l );
		l
	}

	cols (a:%) : SI == rep(a).nbcolumns;

	copy (a:%) : % == 
	{
		(n,m) := dimensions(a);
		rr:DT := new(n*m);
		for i in 1..n*m repeat rr.i := entries(a).i;
		matrix!(n,m,rr);
	}

	elements   (a:%) : (SI,SI,DT) == (rows(a),cols(a),entries(a));

	entries (a:%) : DT == rep(a).data;

	extree (a:%) : ExpressionTree == 
	{
	    import from List ExpressionTree, ExpressionTreeLeaf;
	    (n,m) := dimensions a;
	    v     := entries a;
	    ExpressionTreeMatrix concat! ( 
		[extree leaf n,extree leaf m],
		[(extree (v.i)) for i in 1..n*m]
 	    );
	}

	map! (op: R -> R,a:%) : % == 
	{
		(n,m,da) := elements(a);
		dr:DT := new(n*m);
		for i in 1..n*m repeat dr.i := op(da.i);
		matrix! (n,m,dr);
	}

	matrix (n:SI,m:SI,v:List R) : % ==
	{
		r:DT := new(n*m);
		for i in 1..n*m for l in v repeat r.i := l;
		matrix! (n,m,r);
	}

	matrix (l:List List R) : % ==
	{
		n    := #l;
		m    := #(first l);
		r:DT := new(n*m);
		ll   := l;
		for i in 1..n for k in 1.. by m repeat
		{
			v  := first ll;
			ll := rest ll;
			ASSERT(#v=m);
			for j in k..k+m-1 for e in v repeat r.j := e; 
		}
		matrix! (n,m,r);
	}

	matrix! (n:SI,m:SI,v:DT) : % == 
	{
		ASSERT(n>0);
		ASSERT(m>0);
		per [n,m,v];
	}

	new (n:SI,m:SI,e:R) : % == 
	{
		ASSERT(n>0);
		ASSERT(m>0);
		per [n,m,new(n*m,e)]; 
	}

	random (n:SI, m:SI) : % == 
	{
		rr:DT := new(n*m);
		for i in 1..n*m repeat
			rr.i := (randomInteger()$RandomNumberGenerator)::R;
		matrix!(n,m,rr);
	}

	rows    (a:%) : SI == rep(a).nbrows;

	set! (a:%,i:SI,j:SI, e:R) : R == 
	{
		ASSERT(i>0);
		ASSERT(j>0);
		ASSERT(i<=rows(a));
		ASSERT(j<=cols(a));
		entries(a).(j+(i-1)*cols(a)) := e;
		e;
	}

	submatrix (a:%,r:SI,c:SI,n:SI,m:SI) : % == 
	{
		(an,am) := dimensions(a);
		br:DT := new(n*m);
		b := matrix!(n,m,br);
		for i in 1..n repeat {
			for j in 1..m repeat {	
				b(i,j) := a(r+i-1,c+j-1);
			}
		}
		b;
	}

	times! (c:R,a:%) : % == 
	{
		c=1 => a;
		(n,m) := dimensions(a);
		c=0 => zero(n,m);
		map!( (x:R):R +-> c*x, a );
		--aar := entries(a);
		--for i in 1..n*m repeat aar.i := c*aar.i;
		--a;
	}

	times! (a:%,c:R) : % == 
	{
		c=1 => a;
		(n,m) := dimensions(a);
		c=0 => zero(n,m);
		aar := entries(a);
		for i in 1..n*m repeat aar.i := aar.i*c;
		a;
	}

	transpose (a:%) : % == 
	{
		(n,m) := dimensions(a);
		b:% := new(m,n,0);
		for i in 1..n repeat {
			for j in 1..m repeat {
				b(j,i) := a(i,j);
			}
		}
		b;
	}

	zero (n:SI,m:SI) : % == new(n,m,0);

	zero?(a:%) : Boolean == 
	{
		aa := entries(a);
		for i in 1..rows(a)*cols(a) repeat aa.i ~= 0 => return false;
		true;
	}
}

#if SUMITTEST
-------------------------   test for matdense.as   -------------------------
#include "sumittest"

basic():Boolean ==
{
     macro Z  == Integer;
     macro V  == Vector Z;
     macro MZ == DenseMatrix Z;
     import from Z, V, MZ, List Z, List List Z,SingleInteger;

     a := matrix [[1,2,3],[4,5,6],[7,8,9]];
     b := matrix [[9,8,7],[6,5,4],[3,2,1]];
     v := vector [1,2,3];
     t := new(3,3,1);
     a := add!(a,b);
     a ~= times!(10,t) => false;
     w := b*v;
     w ~= vector [46,28,10] => false;
     7*one(5) ~= map!( (x:Z):Z +-> 7*x, one(5) ) => false;
     b := random(5,7);
     b ~= transpose transpose b => false;
     true;     
}

nullSpace():Boolean ==
{
     macro Z == Integer;
     macro V == Vector Integer;
     macro M == DenseMatrix Integer;
     import from Z,V,M,List V, List Z, List List Z, SingleInteger;
     a          := matrix [[1,2,-1,3],[3,4,-3,7],[5,6,-5,11],[7,8,-7,15]];
     ns:List(V) := nullSpace a;
     r          := rank a;
     (cols a - r) ~= #ns => false;
     for v in ns repeat
     {
          ~zero?(a*v) => return false;
     }
     true;
}

print << "Testing matdense..." << newline;
sumitTest("basic operations", basic);
sumitTest("nullSpace", nullSpace);
print << newline;
#endif
