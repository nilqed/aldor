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
-----------------------   parpol.as   -----------------
#include "sumit.as"

#if ASDOC
\thistype{ParametricPolynomial}
\History {Marco Codutti}{20 June 95}{created}
\Usage   {import from \this(R,a,Px)}
\Params{
        {\em R} & GcdDomain & The ground domain of the parametric coefficients\\
        {\em a} & Symbol    & The parameter name.\\
        {\em P} & UPC       & Some univariate polynomial category \\
}
\Descr   {\this~implements polynomial with parametric coefficients.}
\begin{exports}
gcdIf: & (IF,IF) $\to$ IF & Compute the GCD for the most general case\\
gcdCase: & (P,P,COND) $\to$ CASE & Discuss the GCD for all possible values
     for the parameters\\
\end{exports}
\Aswhere{
UPC  &==& UnivariatePolynomialCategory DenseUnivariatePolynomial(R,a) \\
C    &==& AlgebraicCondition(R,a) \\
IF   &==& If(C,P) \\
CASE &==& Case(C,P) \\
}
#endif

macro Symbol == String;
macro COND   == AlgebraicCondition(R,a);
macro IF     == If(COND,Px);
macro CASE   == Case(COND,Px);

macro Pa == DenseUnivariatePolynomial(R,a);
ParametricPolynomial( R  : GcdDomain,
                      a  : Symbol,
                      Px : UnivariatePolynomialCategory Pa ) : with
{
     gcdIf   : (IF,IF)      -> IF;
#if ASDOC
\aspage    {gcdIf}
\Usage     {\name~(p,q)}
\Signature {(IF,IF)}{IF}
\Params    {{\em p},{\em q} & IF & conditional polynomials \\
           }
\Descr{    compute the GCD of $p$ and $q$ for the most general case, 
           provided that the conditions associated to $p$ and $q$ 
           are fulfilled.
     }
#endif
     gcdCase : (Px,Px,COND) -> CASE;
#if ASDOC
\aspage    {gcdCase}
\Usage     {\name~(p,q,c)}
\Signature {(P,P,C)}{CASE}
\Params    {{\em p},{\em q} & P & parametric polynomials \\
            {\em c}         & C & a condition\\
           }
\Descr{    compute the GCD of $p$ and $q$ for all possible values of the
           parameters provided that condition $c$ is fulfilled.
     }
#endif
}
== add
{
     import from Pa;

     simplify (p:Px,c:COND):Px == apply( (x:Pa):Pa +-> simplify(x,c)$COND, p);

     normalize (p:Px,c:COND):Px ==
     {
          primitivePart simplify(p,c); 
          -- On devrait diviser par le leading term
     }

     gcdCase (uin:Px,vin:Px,cin:COND) : CASE == 
     {
          import from Integer, List Px;
          macro RESUL == Resultant(Pa,Px); 

          c   := copy cin;
          res := empty()$CASE;

          never? c => return res;

          -- step 1 : preliminary computations

          us := simplify(uin,c);
          vs := simplify(vin,c);

          -- step 2 : investigation of the contents

          (contu,u) := primitive us;
          (contv,v) := primitive vs;
          gc        := gcd(contu,contv);

          (condu0,condu1) := fork!(c,contu);
          (condc,condu)   := fork!(condu0,contv);
          (condv,c)       := fork!(condu1,contv);

          res := addNewCase!(res,[condc,0$Px]);
          res := addNewCase!(res,[condu,normalize(vs,condu)]);
          res := addNewCase!(res,[condv,normalize(us,condv)]);

          never? c => return res;
          
          -- Step 3 : simple cases

          if degree u = 0 or degree v = 0 then 
                                        return addNewCase!(res,[c,1$Px]);

          -- Step 4 : investigation of the leading coefficients

          delta := gcd( leadingCoefficient u, leadingCoefficient v );
          (c2,c) := fork!(c,delta);

          res := join!( res, gcdCase(us,vs,c2) );

          never? c => return res;

          -- Step 5 : investigation of the subresultant chain
          lists := SPRS(u,v)$RESUL;

          -- Step 6 : Final efforts

          for S in lists repeat
          {
               lcS    := leadingCoefficient S;
               (c,c2) := fork!(c,lcS);
               res    := addNewCase!( res, [c2,normalize(S,c2)] );
               never? c => return res;
          }

          res := addNewCase!( res, [c,normalize(v,c)] );
          res;
     }

     gcdIf (if1:IF,if2:IF) : IF == 
     {
          import from Integer, COND, Px, Pa, List Px;
          macro RESUL == Resultant(Pa,Px); 

          -- Faiblesses au niveau de la determination du cas le plus general.
          -- On peut utiliser generalCase! mais s'il y a encore des 
          -- specialisations apres, ca peut etre incorrect !!!

          -- step 1 : preliminary computations

          c1 := condition if1;
          c2 := condition if2;
          u1 := object    if1;
          u2 := object    if2;
          us := simplify(u1,c2);
          vs := simplify(u2,c1);
          c  := c1 /\ c2;

          -- step 2 : investigation of the contents

          (contu,u) := primitive us;
          (contv,v) := primitive vs;
          gc        := gcd(contu,contv);

          (cas,c) := generalCase!(c,contu);
          if cas then -- case contu=0 is more general
          {
               (cas,c) := generalCase!(c,contv);
               if cas then return [c,0$Px]; else return [c,normalize(vs,c)];
          }
          else
          {
               (cas,c) := generalCase!(c,contv);
               if cas then return [c,normalize(us,c)];
          }

          -- We put that case outside of the if.
          -- c is c /\ contu~=0 /\ contv~=0;

          -- Step 3 : simple cases

          if degree u = 0 or degree v = 0 then return [c,1$Px];

          -- Step 4 : investigation of the leading coefficients

          delta := gcd( leadingCoefficient u, leadingCoefficient v );
          c     := and!(c,delta~=0);

          -- Step 5 : investigation of the subresultant chain

          S := lastSPRS(u,v)$RESUL;

          -- Step 6 : Final efforts

          lcS := leadingCoefficient S;
          c  := and!(c,lcS~=0);
          return [c,normalize(S,c)];
     }
}

