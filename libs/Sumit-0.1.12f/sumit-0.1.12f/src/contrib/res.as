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
#include "sumit"
macro SI == Integer;
macro Z == Integer;
import from Z,SI,Boolean;

MySPRS(R:IntegralDomain, P:UnivariatePolynomialCategory0 R): with 
      {
        genPseudoRemainder: (P,P) -> (SI,SI,SI,R,R,P);

--	MySPRS: (P,P) -> List P;
        lastMySPRS: (P,P) -> P 

      } == add {


	import from SI,Z;

  genPseudoRemainder (u1:P,u2:P):(SI,SI,SI,R,R,P) == 
      {
	import from MachineInteger;

--  ------ the length of polynomial
           local  poLength(u:P):SI ==
               {
                  if u=0 then 0 else (degree u)+1
               }
 

--#   u,v are full polynomials (trailDegree=0)

       n1:SI := poLength u1;
       n2:SI := poLength u2;
       delta1 := n1 - n2;

       l1 := leadingCoefficient u2;
       t1 := trailingCoefficient u2;

       if relativeSize l1 <= relativeSize t1 
         then 
         {
           w := pseudoRemainder(u1,u2);
           if w ~= 0 then
            {
             d2:SI := trailingDegree w;
             w := shift(w,-d2);
            }
           else d2:SI :=0;
           delta2 := n2-poLength w;
           (delta1,delta2,delta2-d2,l1,t1,w);
         }
       else
        {
           w := pseudoRemainder(revert u1,revert u2);
           if w ~= 0 then
            {
             d1:SI := trailingDegree w;
             w := revert shift(w,-d1);
            }
           else d1:SI :=0;
           delta2 := n2-poLength w;
           (delta1,delta2,delta2-d1,t1,l1,w);
        }
      }

--##########################################
lastMySPRS(u__1:P,u__2:P): P == {

   import from R;

   assert(~zero? u__1); assert(~zero? u__2);
   assert(trailingDegree u__1 =0);
   assert(trailingDegree u__2 =0);
   
   u1 := copy u__1;
   u2 := copy u__2;

   h:R := 1;
   g:R := 1;
   g__:R := 1;
   G:R :=1;
   G__:R :=1;
-- ##
  while u2 ~= 0 repeat
   {
--      uuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuu;
      (w11,w12,w2,w3,w4,w5) := genPseudoRemainder(u1,u2);
      delta := w11;
      delta2:= w12;
      deltas := w2;

      u3 := apply( (x:R):R +-> quotient(x,h^delta*G*g), w5*G__::P);
      TRACE("u3=",u3);

      u1 := u2;
      u2 := u3;

      g := w3;
      g__ := w4;

      h:=quotient(G__*g^delta, G*h^(delta-1));
      TRACE("h=",h);

      G__ := g__^(delta2-deltas);
      G := g^(delta2-deltas);
      
--#
    }
  u1
  }
}
