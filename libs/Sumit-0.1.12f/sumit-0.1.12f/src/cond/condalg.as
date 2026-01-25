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
------------------------------   condalg.as   ------------------------------
#include "sumit"

#if ASDOC
\thistype{AlgebraicCondition}
\History {Marco Codutti}{20 June 95}{created}
\Usage   {import from \this(R,x)}
\Params{
        {\em R} & GcdDomain & The ground domain of the algebraic expressions\\
        {\em x} & Symbol    & The parameter.\\
}
\Descr   {\this~implements algebraic condition on parameters,
          that is combinations of $P=0$ and $P\not=0$ where $P$ belong 
          to DenseUnivariatePolynomial(R,x).}
\begin{exports}
\category{ConditionCategory}\\
= : & (P,P) $\to$ \%  & assert that two parametric expressions are identical\\
\~{}=: & (P,P) $\to$ \%  & assert that two parametric expressions are different\\
fork!: & (\%,P) $\to$ (\%,\%) & specialize a condition\\
generalCase!: & (\%,P) $\to$ (Boolean,\%) & return the most general case\\
simplify: & (P,\%) $\to$ P & simplify a parametric expression under a condition\\
zeroCase?: & \% $\to$ Boolean & check if a condition is of the kind $P=0$\\
\end{exports}
\Aswhere{ P &==& DenseUnivariatePolynomial(R,x) \\ }
#endif

macro SI   == SingleInteger;
macro Z    == Integer;
macro TEXT == TextWriter;
macro TREE == ExpressionTree;
import from SI,Z,TEXT,TREE;

macro P == DenseUnivariatePolynomial(R,x);
AlgebraicCondition( R: GcdDomain, x: String) : ConditionCategory with
{
     =:             (P,P) -> %;
#if ASDOC
\aspage    {=}
\Usage     {a=b}
\Signature {(P,P)}{\%}
\Params    {{\em a}, {\em b} & P & parametric expressions}
\Descr     {build a new condition which stipulates that $a=b$}
#endif
     ~=:            (P,P) -> %;
#if ASDOC
\aspage    {\~{}=}
\Usage     {a \name~b}
\Signature {(P,P)}{\%}
\Params    {{\em a}, {\em b} & P & parametric expressions}
\Descr     {build a new condition which stipulates that $a\not=b$}
#endif
     fork!:         (%,P) -> (%,%);
#if ASDOC
\aspage    {fork!}
\Usage     {\name~(c,p)}
\Signature {(\%,P)}{(\%,\%)}
\Params    {{\em p} & P  & a parametric expression \\
            {\em c} & \% & a condition \\
           }
\Retval    {$(a,b)$, where $a$ is $c \wedge(P=0)$ and $b$ is 
            $c \wedge (P\not=0)$.
            }
\Descr     {In-place operation. c is destroyed.}
#endif
     generalCase!:   (%,P) -> (Boolean,%);
#if ASDOC
\aspage    {generalCase!}
\Usage     {\name~(c,p)}
\Signature {(\%,P)}{(Boolean,\%)}
\Params    {{\em p} & P  & a parametric expression \\
            {\em c} & \% & a condition \\
           }
\Retval    {$(z,d)$, where $d$ is the most general case between 
            $c \wedge P=0$ and $c \wedge P\not=0$. 
            $z$ is {\em true} if the most general case is $c \wedge P=0$.
            }
\Descr     {In-place operation. c is destroyed.}
#endif
     simplify:      (P,%) -> P;
#if ASDOC
\aspage    {simplify}
\Usage     {\name~(p,c)}
\Signature {(P,\%)}{P}
\Params    {{\em p} & P  & a parametric expression \\
            {\em c} & \% & a condition \\
           }
\Descr     {simplifies $p$ so that it respects condition $c$.}
#endif
     zeroCase?:         %  -> Boolean;
#if ASDOC
\aspage    {zeroCase?}
\Usage     {\name~c}
\Signature {\%}{Boolean}
\Params    {{\em c} & \% & a condition \\}
\Descr     {test if a condition is of the form $P=0$.}
#endif
}
== add
{
     -- notzero part should be a set, not a list.
     macro Rep == Union( zero:P, notzero:List P );
     import from P,List P,Rep;

     -- Internals

     zcase? (c:%)      : Boolean == rep(c) case zero;
     nzcase?(c:%)      : Boolean == rep(c) case notzero;
     zpart  (c:%)      : P       == rep(c).zero;
     nzpart (c:%)      : List P  == rep(c).notzero;
     zcond  (p:P)      : %       == per union p;
     nzcond (p:List P) : %       == per union p;
     sqfree (p:P)      : P       == { 
          (g,gp,gd) := gcdquo(p,differentiate p);  
          gp; 
     }

     (c1:%) = (c2:%) : Boolean ==
     {
          zcase? c1  and zcase?  c2 => return zpart c1 = zpart c2;
          nzcase? c1 and nzcase? c2 =>
          {
               nz1 := nzpart c1;
               nz2 := nzpart c2;
               (#nz1 ~= #nz2)$SingleInteger => return false;
               for p1 in nz1 repeat ~member?(p1,nz2) => return false;
               return true;
          }     
          return false;
     }

     (p1:P)  = (p2:P) : % ==  zcond sqfree (p1-p2);
     (p1:P) ~= (p2:P) : % ==  {
          t := sqfree (p1-p2);
          zero? t => Never();
          one? t => Always();
          nzcond [t];
     }

     ~ (c:%) : % ==
     {
          always? c => Never();
          never?  c => Always();
          zcase?  c => nzcond [zpart c];
          zcond reduce( (a:P,b:P):P +-> a*b, nzpart c, 1 );
     }

     (c1:%) /\ (c2:%) : % == and!( copy c1, c2 );

     (p:TEXT) << (c:%) : TEXT == tex(p,extree c);

     Always ()    : %       == zcond 0;
     always? (c:%) : Boolean == zcase? c and zpart c = 0;

     and! (c1:%,c2:%) : % == 
     {
          never? c1 or never? c2 => Never();
          always? c1             => c2;
          always? c2             => c1;
          
          res := c1;
          if zcase? c2 then return assertZero!(zpart c2, res)
          else
          {
               for nz in nzpart c2 repeat res := assertNotZero!(nz,res);
               return res;
          }
     }

     -- Internal : c <- c and p<>0. Assume p sqfree and c<>true,false.
     assertNotZero! (p:P,c:%) : % ==
     {
          import from Z;
          if nzcase? c then
          {
               sp        := sqfree p;
               nzlist    := nzpart c;
               newnzlist := [p]$List(P);
               for curnz in nzlist repeat
               {
                    (g,nz,gp) := gcdquo(curnz,p);
                    degree(nz) = 0 => iterate;
                    newnzlist := cons(nz,newnzlist);
               }
               nzcond newnzlist;
          }
          else
          {
               z        := zpart c;
               (g,z,gp) := gcdquo(z,p);
               if degree z = 0 then Never() else zcond z;
          }
     }

     -- Internal : c <- c and p=0. Assume p sqfree and c<>true,false.
     assertZero! (p:P,c:%) : % == 
     {
          import from Z;

          if nzcase? c then
          {
               z := p;
               for nz in nzpart c repeat
               {
                    (g,z,gnz) := gcdquo(z,nz);
                    degree z = 0 => return Never();
               }
               zcond z;
          }
          else
          {
               z := zpart c;
               g := gcd(z,p);
               if degree g = 0 then Never() else zcond g;
          }
     }

     copy (c:%) : % ==
     {
          import from List P;
          zcase? c => zcond copy zpart c;
          nzcond copy nzpart c; 
     }

     extree (c:%) : TREE ==
     {
          import from List TREE, ExpressionTreeLeaf;

          always? c => extree leafString "always";
          never?  c => extree leafString "never";
          zcase?  c => ExpressionTreeEqual [extree zpart c, extree 0$P];
          ExpressionTreeAnd [ ExpressionTreeNotEqual [extree p, extree 0$P] 
               for p in nzpart c];
     }

     fork!  (c:%,p:P) : (%,%) == {
          t := sqfree(p);        
          always? c => (t=0,t~=0);
          never?  c => (Never(),Never());
          (assertZero!(t,copy c), assertNotZero!(t,c));
     }

     generalCase! (c:%,p:P) : (Boolean,%) ==
     {
          always? c => return (false,p~=0);
          never?  c => return (true,Never());

          if ~zeroCase? c then 
          {
               return (false,and!(c,p~=0));
          }
          else 
          {
               (c5,c6) := fork!(c,p);
               never? c6 => return (true,c5);
               if degree zeroPart c5 > degree zeroPart c6 then 
                   return (true,c5);
               else
                   return (false,c6);
          }
     }

     Never ()    : %       == zcond 1;
     never? (c:%) : Boolean == zcase? c and one? zpart c;
     sample       : %       == Always();

     simplify (p:P,c:%) : P ==
     {
          never?  c => p;
          always? c => p;
          nzcase? c => p;
          (q,r) := pseudoDivide(p,zpart c);
          r;
	}

     zeroCase? (c:%) : Boolean == zcase? c;

     -- Not used in this release
     zeroPart  (c:%) : P       == zpart c;
}

#if SUMITTEST
-------------------------   test for condalg.as   -------------------------
#include "sumittest.as"

test():Boolean ==
{
     macro Z == Integer;
     macro P == DenseUnivariatePolynomial(Z,"a");
     macro C == AlgebraicCondition(Z,"a");
     import from Z,P,C;

     a:P := monomial(1,1);
     c:C := (a-1)*(a-2::P)*(a-3::P)=0;
     p:P := (a-1)*(a-2::P);
     (b,d) := generalCase!(c,p);
     b and d=(p=0);
}

print << "Testing condalg..." << newline;
sumitTest("algebraic conditions", test);
print << newline;
#endif
