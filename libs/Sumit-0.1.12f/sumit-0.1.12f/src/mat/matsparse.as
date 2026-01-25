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
------------------------------   matsparse.as   ------------------------------
#include "sumit"

#if ASDOC
\thistype{SparseMatrix}
\History {Marco Codutti}{10 June 1995}{created}
\Params  {{\em R} & SumitRing & The coefficient ring of the matrices.}
\Descr   {\this~ is an implementation of sparse matrices.}
\begin{exports}
\category{MatrixCategory~R} \\
\end{exports}
#endif

SparseMatrix (R:SumitRing) : MatrixCategory(R) == add {
     macro SI  == SingleInteger;
     macro P   == SparseUnivariatePolynomial(R,"x");
     macro A   == PrimitiveArray P;
     macro V   == Vector R;
     macro Rep == Record( nbrow:SI, nbcolumn:SI, mat:A );
     import from SI,P,A,R,Rep;

     -- Internals macro to take parts of, or build sparse matrices.
     macro row(a,i)			== rep(a).mat.i;
     local matrix!(n:SI,m:SI,a:A):%	== per [n,m,a];

	(a:%) = (b:%) : Boolean == 
	{
		(n,m) := dimensions a;
		(n ~= rows(b)) or (m ~= cols(b)) => false;
		for i in 1..n repeat row(a,i) ~= row(b,i) => return false;
		true;
	}

     (a:%) * (v:V) : V ==
     {
          import from UnivariateMonomial R,Integer;
          n := rows a;
          m := cols a;
          ASSERT(m=#v);
          r := zero(n)$V;
          for i in 1..n repeat
          {
               t := r.i;
		ASSERT zero? t;
               for mon in row(a,i) repeat 
               {
                    (c,d) := mon;
                    t := add!(t, c * v(d::SI));
               }
               r(i) := t;
          }
          r;          
     }

	(a:%) * (b:%) : % == 
	{
		(na,ma) := dimensions(a);
		(nb,mb) := dimensions(b);
		ASSERT(ma=nb);
		r := zero(na,mb);
		for i in 1..na repeat
               for mon in row(a,i) repeat
               {
                    (c,d) := mon;
		          for j in 1..mb repeat r(i,j) := r(i,j) + c*b(d::SI,j);
		    }
		r;
	}			

	add! (a:%,b:%) : % == 
	{
		(n,m)   := dimensions(a);
		(nb,mb) := dimensions(b);
		ASSERT(n=nb);
		ASSERT(m=mb);
		for i in 1..n repeat row(a,i) := add!(row(a,i),row(b,i));
		a;
	}

     apply (a:%,i:SI,j:SI) : R ==
     {
          import from Integer;
          ASSERT(i>0);
          ASSERT(j>0);   
          ASSERT(i<=rows(a));
          ASSERT(j<=cols(a));
          coefficient( row(a,i), j::Integer );
     }

     cols (a:%) : SI == rep(a).nbcolumn;

     copy (a:%) : % ==
     {
          pa := new(rows a)$A;
          for i in 1..rows(a) repeat pa.i := copy row(a,i);
          matrix!(rows a, cols a, pa);
     }

	diagonal? (a:%) : Boolean == 
	{
		for i in 1..rows(a) repeat 
          {
               (degree row(a,i))::SI ~= i => return false;
               ~monomial?(row(a, i))      => return false;
          }
		true;
	}

	minus!(a:%) : % ==
     {
          for i in 1..rows(a) repeat row(a,i) := times!(-1$R,row(a,i));
          a;
     }

	one? (a:%) : Boolean == 
	{
		for i in 1..rows(a) repeat 
          {
               (degree row(a,i))::SI ~= i         => return false;
               ~one? leadingCoefficient row(a,i)  => return false;
               ~monomial?(row(a, i))              => return false;
          }
		true;
	}

     random( n:SI, m:SI ) : % == random( n,m,max(n,m) );
     random( n:SI, m:SI, nb:SI ) : % ==
     {
          import from Integer,R,RandomNumberGenerator;
          a:% := zero(n,m);
          for k in 1..nb repeat
          {
               gi := randomGenerator(1,1,n::Integer);
               gj := randomGenerator(1,1,m::Integer);
               i:SI := retract apply gi;
               j:SI := retract apply gj;
               a(i,j) := (randomInteger())::R;
          }
          a;
     }

     rows (a:%) : SI == rep(a).nbrow;

	rowSwap! (a:%,i1:SI,i2:SI,j1:SI,j2:SI ): % ==
	{
          t         := row(a,i1);
          row(a,i1) := row(a,i2);
          row(a,i2) := t;
          a;
     }

     set! (a:%,i:SI,j:SI,r:R) : R ==
     {
          import from Integer;
          ASSERT(i>0);
          ASSERT(j>0);
          ASSERT(i<=rows(a));
          ASSERT(j<=cols(a));
          e := r - coefficient( row(a,i), j::Integer );
          row(a,i) := add!(row(a,i),e,j::Integer);
          r;
     }

     substract! (a:%,b:%) : % == 
	{
		(n,m)   := dimensions(a);
		(nb,mb) := dimensions(b);
		ASSERT(n=nb);
		ASSERT(m=mb);
		for i in 1..n repeat row(a,i) := add!(row(a,i),-1$R,0$Integer,row(b,i));
		a;
	}

	times! (c:R,a:%) : % == 
	{
		c=1 => a;
		(n,m) := dimensions(a);
		c=0 => zero(n,m);
          for i in 1..n repeat row(a,i) := times!(c,row(a,i));
          a;
	}

	transpose (a:%) : % == 
	{
          import from Integer;
          b := zero(cols(a),rows(a));
		for i in 1..rows(a) repeat
			for mon in row(a,i) repeat
               {
                    (c,d0) := mon;
                    b(retract d0,i) := c;
               }
		b;
	}

     zero (n:SI,m:SI) : % ==
     {
          pa := new(n)$A;
          for i in 1..n repeat pa.i := 0$P;
          matrix!(n,m,pa);
     }

	zero?(a:%) : Boolean == 
	{
		for i in 1..rows(a) repeat row(a,i) => return false;
		true;
	}
}

#if SUMITTEST
-------------------------   test for matsparse.as   -------------------------
#include "sumittest"

basic():Boolean ==
{
     macro Z  == Integer;
     macro V  == Vector Z;
     macro MZ == SparseMatrix Z;
     import from Z, V, MZ, List Z, List List Z, SingleInteger;

     a := random(3,3);
     b := zero(3,3);
     b(1,1) := 1; b(2,2) := 2; b(3,3) := 3;
     c := a+b;
     a := minus!(a);
     a := substract!(a,b);
     a := minus!(a);
     a ~= c => false;
     v := vector [1,2,3];
     w := b*v;
     w ~= vector [1,4,9] => false;
     7*one(5) ~= map!( (x:Z):Z +-> 7*x, one(5) ) => false;
     b := random(5,7);
     b ~= copy b => false;
     b ~= transpose transpose b => false;
     true;     
}

nullSpace():Boolean ==
{
     macro Z == Integer;
     macro V == Vector Integer;
     macro M == SparseMatrix Integer;
     import from Z,V,M,List V,SingleInteger;
     a := random (5,7);
     ns:List(V) := nullSpace a;
     r          := rank a;
     (cols a - r) ~= #ns => false;
     for v in ns repeat
     {
          ~zero?(a*v) => return false;
     }
     true;
}
print << "Testing matsparse..." << newline;
sumitTest("basic operations", basic);
sumitTest("nullSpace", nullSpace);
print << newline;
#endif
