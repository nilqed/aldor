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
#include "sal_set2.as"

macro Z    == Integer;
macro SI == SingleInteger;
macro LeadTrailFlag == Enumeration(Lead, Trail);
macro MatK == DenseMatrix K;
macro Constraint == Record(root: Z, eq: MatK);
macro Constraints == List Constraint;
macro PERM == PrimitiveArray SI;
macro  SetZ == (List Integer);
macro  ArrSZ == PrimitiveArray SetZ;

EGeliminations(K: IntegralDomain, R: UnivariatePolynomialCategory K,
               MatR: MatrixCategory R): with
     {      
        getTrapezForm!: (MatR, SI, LeadTrailFlag) ->
				      (Constraints,ArrSZ,PERM);
     } == add{	  
     import from R, MatR, Constraint, Constraints,List RationalRoot,
                 K,MatK,SI,Z,Boolean,Vector R,ArrSZ,SetZ,TextWriter,
								 Integer;
								 
			local elemSwap!(a:ArrSZ,i:SI,j:SI):ArrSZ ==
			   {
   				 temp:SetZ := a(i);
	  			 a(i) := a(j);
		  		 a(j) := temp;
				 
			  	 a
				 }					 
								 
								 
--    -----------------------------------		  
		 local getConstraints(v1:MatR,p:SetZ): Constraints ==
		   {
			   local res: Constraints := [];
         local v:MatK := zero(1,cols v1);
			 
--			  print<<"Check GetConstrs: set= "<<p<<newline;
			 
			  for local w:Integer in p repeat
			     {
--					  print << "GetConstrs: w= " << w <<newline;
			      for local j:SI in 1..(cols v1) repeat
			        {
			      	 temp:R := apply(v1,1,j);
			         set!(v,1,j,apply(temp, w::K));
              }
			      res := cons([w,copy v], res);
			     }
					 
--			  print << "GetConstrs: res= " << res<<newline;
			  res;
				
			 }
------------------------------------------------------------------
    local performEGij!(P:MatR, i:SI, j:SI, c:SI, lt:LeadTrailFlag, 
                               m:SI,nblocks:SI
							  					    ,excludedZ:ArrSZ,constrs:Constraints
															 ):(Constraints,ArrSZ) ==
------------------------------------------------------------------
--             performs elimination in i-th row by j-th
------------------------------------------------------------------
           {
       a := apply(P,i,c);
       if a~=0 then
         {
		      if lt = Lead then
           {
            u := leadWidth(P,i,m,nblocks);
            v := leadWidth(P,j,m,nblocks);
           }
          else
           {
            u := trailWidth(P,i,m,nblocks);
            v := trailWidth(P,j,m,nblocks);
           }

         if u < v then
          {
           rowSwap!(P,i,j);
           elemSwap!(excludedZ,i-1,j-1);
           performEGij!(P,i,j,c,lt,m,nblocks,excludedZ,constrs);
          }
         else
          {
           b := apply(P,j,c);
	         w:MatR := apply(P,i,1,1,cols P);
           rowCombine!(P, b,i, -a,j);
--					 print <<"MAIN rowComb: "<<newline << P << newline;

           iroots:List RationalRoot := integerRoots b;
--					 print<<"Check RatRoots: b="<<b<<"; roots: "<<iroots<<newline;
           w1:SetZ := [];
						
					 for r:RationalRoot in iroots repeat
			        w1:=union!(w1, integerValue(r));
						                 
				   w1:=union!(w1,minus(excludedZ(j-1),excludedZ(i-1)));
			     excludedZ(i-1):=union!(excludedZ(i-1),excludedZ(j-1));
					 w2:List R := coerce row(P,i);
					 assert(R has GcdDomain);
					 (cf:R,w4:List R):=gcdquo(w2);

--           print << "Check gcd: row= "<<w2<<" ; gcd= "<<cf<<newline;
					 						
					 iroots2:List RationalRoot := integerRoots cf;
--					 print<<"Check RatRoots: cf="<<cf<<"; roots: "<<iroots2<<newline;
           w3:SetZ := [];
						
					 for r in iroots2 repeat
			        w3:=union!(w3, integerValue(r));
					 
					 excludedZ(i-1):=union!(excludedZ(i-1),w3);
					 set!(P,i,1,transpose(coerce vector(w4)));
					 
					 constrs:=concat!(constrs,getConstraints(w,w1));
           (constrs,excludedZ)
		      }
		    }     
		   else
		    {
--		   TRACE("perform: nothing to do",P);
		     (constrs,excludedZ);
		    } 
     }
----------------------------------------------
-- ####################################################################
     local performEGbyPrev!(P: MatR, w1:SI, m:SI,lt:LeadTrailFlag,
                            nblocks:SI,base:SI,p:PERM
														  ,excludedZ:ArrSZ,constrs:Constraints
														):(Constraints,ArrSZ) ==
---------------------------------------------------------------------------
--               performs elimination in (w1+1)-th row by all previous ones
---------------------------------------------------------------------------
    {

       for j:SI in 1..w1 repeat
		      {
		       TRACE("by j=",j);
		       TRACE("whom i=",w1+1);
					 (constrs,excludedZ):=
					 performEGij!(P,w1+1,j,base+p(j-1),lt,m,nblocks,excludedZ,constrs);
--					 print <<"MAIN: "<<newline << P << newline;
		      }
--			print << "ByPrev: constrs= "<<constrs<<newline; 
       (constrs,excludedZ)
   }
--#####################################################################
              local leadWidth(P:MatR, r:SI, m:SI, nblocks:SI): SI ==
                  {
                    j := nblocks;
                    while zero? apply(P,r,j*m-m+1,1,m) and j>0 repeat
                      j := j-1;
                   j
                  }
--       -------------------------------------------------------------
              local trailWidth(P:MatR,r:SI,m:SI, nblocks:SI): SI ==
                 {
                    j := nblocks;
                    while zero? apply(P,r,(nblocks-j)*m+1,1,m) and j>0 repeat
                      j := j-1;
                   j
                  }

--#####################################################################
								local	add1(l:SetZ):SetZ == 
									  {
											if #l=0 then []
													 else
														 cons(l(first)+1,add1(rest l))
									  }
												
								local	subtr1(l:SetZ):SetZ == 
									  {
											if #l=0 then []
													 else
														 cons(l(first)-1,subtr1(rest l))
									  }					 


      
              local shiftRow!(P: MatR,excludedZ:ArrSZ, r: SI, lt:LeadTrailFlag,
							                 nblocks:SI,m:SI):ArrSZ ==
                  {
									
                   if lt = Lead 
                    then 
                      {
                       for i:SI in 1..(nblocks-1)*m repeat
                         {
                          temp := apply(P,r,i+m);                 
                          set!(P,r,i,apply(temp,monom+1));
                         }
                       for i in ((nblocks-1)*m+1)..nblocks*m repeat
                         {
                          set!(P,r,i,0)
                         }
											 excludedZ(r):=subtr1(excludedZ(r))
                      }
                    else
                      {
                       for i:SI in nblocks*m..m+1 by -1 repeat
                         {
                          temp := apply(P,r,i-m);
                          set!(P,r,i,apply(temp,monom-1));
                         }
                       for i in 1..m repeat
                         {
                          set!(P,r,i,0)
                         }
											 excludedZ(r):=add1(excludedZ(r))
                      }
									 excludedZ		
                  }
-- ####################################################################
  getTrapezForm!(P:MatR, m:SI, lt:LeadTrailFlag): 
	           (Constraints,ArrSZ,PERM) ==
      
--   P is explicit matrix
--   m is number of variables
    {
     nblocks:SI := cols P quo m;

     if lt = Lead 
      then 
       {
        base:SI := 0;
       }
      else
       {
        base:SI := cols P - m;
       }

     p:PERM := new(m);
     for i:SI in 1..m repeat p(i-1):=i;
		 
     excludedZ: ArrSZ := new rows P;
     for i:SI in 1..(rows P) repeat excludedZ(i-1):=[];

     w1:SI := 0;
     w2:SI := rows P;
		      
     while zero? apply(P, w2, 1, 1, cols P) repeat
         w2 := w2-1;
		      
     constrs:Constraints := [];
     ThatsAll:Boolean := false;

--     print <<"MAIN: "<<newline << P << newline;
		      
     while w1 < w2 repeat
      {
			 TRACE("w1=",w1);
			 TRACE("w2=",w2);
			          
			 (constrs,excludedZ):=
			         performEGbyPrev!(P, w1, m,lt,nblocks,base,p,excludedZ,constrs);
--       print <<"MAIN: "<<newline << P << newline;
--  ###             get nonzero row  ########
       while zero? apply(P, w1+1, 1, 1, cols P) repeat
        {
			    if w2>w1+1 then
			      {
             rowSwap!(P,w1+1,w2);
						 
--						 print <<"MAIN: "<<newline << P << newline;
						 
						 excludedZ:=elemSwap!(excludedZ,(w1+1)-1,w2-1);
             w2 := w2 - 1;
			       TRACE("rows swaped, w2=",w2);
			       TRACE("P=",P);
			      }
			    else
			      {
			       ThatsAll := true; 
			       break;
			      }
        }

      if ThatsAll then break;

--   ##             shift it if neccesary   ####
     if zero? apply(P,w1+1,base+1,1,m) then
		        {
              while zero? apply(P,w1+1,base+1,1,m) repeat
                 {
			              TRACE("shifting, before=",P);
                    excludedZ := shiftRow!(P,excludedZ, w1+1, lt,nblocks,m);
--										print <<"MAIN: "<<newline << P << newline;
			              TRACE("shifting, after=",P);
                 }
		     	    iterate;
			      }

--   ####  now the (w1+1)-th row in the trail (lead) part is nonzero
      i:SI := w1+1;
      while zero? apply(P, w1+1, base+p(i-1)) repeat
			     i := i+1;

			 if i ~= w1+1 then 
		      { 
--				      exchangeVariables!(P, w1+1,i,nblocks,m);
--                               note the exchange
            temp:=p(i-1);
            p(i-1):=p((w1+1)-1);
            p((w1+1)-1):=temp;					
	        }
--			print << "main: constrs=" << constrs << newline;
			w1 := w1+1;
     }
		    TRACE("end, w1=",w1);
		    TRACE("end, w2=",w2);   
        (constrs,excludedZ,p);
   }
  }
-- ##########################################################################
