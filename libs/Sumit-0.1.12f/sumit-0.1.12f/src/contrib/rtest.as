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
-----------------------------
#include "sumit"
--#include "sallinterp"
-- #include "rand.as";
#library MYRES "res.ao";
import from MYRES;

-- initGen();

macro I == MachineInteger;
macro Z == Integer;
macro NTIMES == 5@Z;
macro DELTA == 1@Z;
macro DEGREE1 == 7@Z;

import from Z, Symbol, String;
macro Zy == DenseUnivariatePolynomial(Z);
macro Zyx == DenseUnivariatePolynomial(Zy);
import from Zyx,Zy;
import from MySPRS(Zy,Zyx);
import from Timer;
import from TextWriter,WriterManipulator,TextReader;
-------------------------------
main0(variant:Z):(I,I) == {

t1 := timer();
t2 := timer();

d:Z := DEGREE1;
--------------------------
p:Zyx:=random(d);
--stdout << p << endnl;
for i:Z in 0..d repeat
  {
   if variant = 1 then 
      {
        temp:Zy:=random(2+3*(i+1)*(d-i));
      }
   else 
    if variant = 2 then
     { 
      temp:Zy:=random(3+3*(d-i));
     }  
   else 
    if variant = 3 then
     { 
      temp:Zy:=random(3+3*(i));
     }  
   else 
    if variant = 4 then
     { 
      temp:Zy:=random(2+3*(d-i+1)*i);
     }  
   else 
    if variant = 5 then
     { 
      temp:Zy:=random(1+2*(d-i)*i);
     }  
   
   stdout << degree temp << endnl;
--   stdout<<"Setting polynomials: temp="<<temp<<endnl;   
   setCoefficient!(p,d-i,temp);
  }
stdout << "---------------------"<<endnl;
q:Zyx:=random(d-DELTA);
for i:Z in 0..(d-DELTA) repeat
  {
   if variant = 1 then 
      {
        temp:Zy:=random(2+2*(i+1)*(d-DELTA-i));
      }
   else 
    if variant = 2 then
     {
      temp:Zy:=random(2+2*(d-DELTA-i));
     }
   else 
    if variant = 3 then
     {
      temp:Zy:=random(2+2*(i));
     }
   else 
    if variant = 4 then
     {
      temp:Zy:=random(2+2*(d-DELTA-i)*i);
     }
   else 
    if variant = 5 then
     {
      temp:Zy:=random(2+2*(d-DELTA-i)*i);
     }

   stdout << degree temp << endnl;
   setCoefficient!(q,d-DELTA-i,temp);
  }

--x:Zyx:=monom;
--q:=q*x+x^0;
-----------
for i in 1..NTIMES repeat {
start! t1; r := resultant(p, q); stop! t1;
start! t2; t := lastMySPRS(p, q); stop! t2;
}
----------
stdout << "--------------------------" << endnl <<  quotient(r::Zyx,t) <<endnl;
--stdout << (r::Zyx)-t<<endnl;

(read t1, read t2);
}
-----------
main():() == {
	import from I,Z;

  for i:Z in 1..5 repeat {
   	(c1, c2) := main0(i);
    stdout << "Variant : " << i << endnl;
    stdout << "Time for resultant = " << c1::Z quo NTIMES << endnl;
	  stdout << "Time for lastMySPRS = " << c2::Z quo NTIMES << endnl;
    stdout << "--------------------" << endnl;
  }
}
---
main();
--
