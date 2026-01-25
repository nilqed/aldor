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
-- #########         TESTS           ###########################
#include "sumit";
#library EG "egelim.ao";
#include "rand.as"
import from EG;

macro Z    == Integer;
macro Zn == DenseUnivariatePolynomial (Z, "n");
macro MatZn == DenseMatrix Zn;
macro SI == SingleInteger;
macro MatZ == DenseMatrix Z;
macro ArrMZn == PrimitiveArray MatZn;
macro Constraint == Record(root: Z, eq: MatZ);
macro LeadTrailFlag == Enumeration(Lead, Trail);
macro Constraints == List Constraint;
macro NUMOFTESTS == 6;


main():() == {

  import from Z, Zn, MatZn, List Zn, MatZ, SI,EGeliminations(Z,Zn,MatZn), 
  List List Zn, LeadTrailFlag, Constraints, Constraint, ArrMZn,
	PrimitiveArray Integer,PrimitiveArray LeadTrailFlag;

  import from TextWriter, List RationalRoot;

  n := monom@Zn;

  zero:= (0@Z)::Zn;
  one := (1@Z)::Zn;
  two := (2@Z)::Zn;

  Sys:ArrMZn := new NUMOFTESTS;
	NumOfVars: PrimitiveArray SingleInteger := new NUMOFTESTS;
	Where: PrimitiveArray LeadTrailFlag := new NUMOFTESTS;
---------------------------------------
  Sys(1-1) := matrix([[n-one,0,  0,0,      0,0,  0,-one],
                      [-two, 0,  0,n-two,  0,0,  0,   0]]);
  NumOfVars(1-1):=2;
	Where(1-1):=Lead;
---------------------------------------
  Sys(2-1) := matrix([[n-one,0,  0,0,      0,0,  0,-one],
                      [-two,0,   0,n-two,  0,0,  0,0]]);
  NumOfVars(2-1):=2;
	Where(2-1):=Trail;
---------------------------------------
  Sys(3-1) :=     matrix([[n^2+n,0,         one,      one],
                          [n^2+n,0,           0, -n-one],
			                    [one,  n+3*one,     0,     0]]);
  NumOfVars(3-1):=2;
	Where(3-1):=Lead;
---------------------------------------	
	Sys(4-1):=  matrix([[n+one,0,  -1,-1],
                      [0,n+one,   -1,-1]]);
  NumOfVars(4-1):=2;
	Where(4-1):=Trail;
---------------------------------------
	Sys(5-1):=  matrix([[0,0,      -20*n-40*one,two,  n+3*one,0],
                      [0,n+one,       -one,   0,  0,0]]);
  NumOfVars(5-1):=2;
	Where(5-1):=Lead;
---------------------------------------
	Sys(6-1):=  matrix([[-100*n-100*one,0,   0,two,      n-one,0,       0,0],
                      [0,-100*n-100*one,       100*one,0,  0,n-5*one,  -one,0]]);
  NumOfVars(6-1):=2;
	Where(6-1):=Trail;
---------------------------------------
  for i:SI in 1..NUMOFTESTS repeat 
	  {
     print << "Original system:" << newline;
     print << Sys(i-1) << newline;
     (constrs:Constraints, exZ:PrimitiveArray List Integer ,
		       perm: PrimitiveArray SingleInteger) :=
		            getTrapezForm!(Sys(i-1),NumOfVars(i-1),Where(i-1));
     print << "Converted in the "<<Where(i-1)<<"ing part to:" << newline;
     print << Sys(i-1) << newline;
     print << "constraints:" << newline;
     for j:SI in 1..#constrs repeat
     print << "root: " << constrs.j.root << "; eq: " 
		       << constrs.j.eq << newline;  

     print << "Excluded values:" << newline;
     for j:SI in 1..rows Sys(i-1) repeat
     print << exZ(j-1) << newline;  

     print << "permutation:" << newline;
		 for j:SI in 1..NumOfVars(i-1) repeat
     print << perm(j-1)<< " ";
     print << newline;
		 
     print << "--------------------------------" << newline;
    }

}

main();

