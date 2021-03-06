--------------------------------------------------------------------------------
--
-- sm_polring.as: A category constructor to define polynomial domains
-- either as finite abelian monoid rings (as in AXIOM or most computer algebra
-- systems) or simply as the results of repeated itersations of the rule
-- `R -> R[X]' (as in classical algebra textbooks) without building monomials
-- explicitely.
--
--------------------------------------------------------------------------------
--  Copyright (c) 1990-2007 Aldor Software Organization Ltd (Aldor.org).
-- Copyright: INRIA, and University of Lille I, 2001
-- Copyright: Marc Moreno Maza
--------------------------------------------------------------------------------

-- cat PolynomialRing

#include "algebra"


macro { 
        NNI == Integer;
        UPR == IndexedFreeAlgebra(R,NNI);
        UPP == IndexedFreeAlgebra(%,NNI);
        SUP == SparseUnivariatePolynomial;
        ECATV == ExponentCategory(V);
        FAMR == FiniteAbelianMonoidRing0;
}

+++ `PolynomialRing(R,V)' is the category of the domains that implement
+++ a polynomial ring with coefficients in `R' and variables in `V'.
+++ If `V' is a finite set `{v1,...,vl}' this polynomial ring is just
+++ `R[v1,...,vl]'. If `V' is finite or not, the set of monomials is
+++ the free abelian monoid `E' generated by `V'. Moreover `E' is
+++ totally ordered by the lexicographical ordering induced by `V'.
+++ Author: Marc Moreno Maza
+++ Date Created: 09/12/97
+++ Date Last Update: 14/11/04 (Xin Li and MMM)
+++ Keywords: polynomial, variable, degree, eval, differentiate, algebra

define PolynomialRing(R:Join(ArithmeticType, ExpressionType),
                      V: Join(TotallyOrderedType, ExpressionType)): Category == 
 PolynomialRing0(R,V) with {
	eval: (%, V, R) -> %;
	  ++ `eval(p, v, r)' evaluates p at r as a univariate polynomial in v.
	eval: (%, V, %) -> %;
	  ++ `eval(p, v, q)' evaluates p at q as univariate polynomial in v.
	eval: (%, List V, List R) -> %;
	  ++ `eval(p, lv, lr)'  assumes that `lv' and `lr' have the same
          ++ length. Then returns `p' if `lv' and `lr' are empty.
          ++ Otherwise returns `eval(eval(p,first lv, first lr),rest lv, rest lr)'.
	eval: (%, List V, List %) -> %;
	  ++ `eval(p, lv, lp)' assumes that `lv' and `lp' have the same
          ++ length. Then returns `p' if `lv' and `lp' are empty.
          ++ Otherwise assuming that `lv.i' is the rightmost among the greatest 
          ++ variables in `lv', returns `eval(eval(p,lv.i,lp.i),lu,lq)'
          ++ where `lu' and `lq' are obtained from `lv' and `lp' by
          ++ removing `lv.i' and `lp.i' respectively. 
          ++ N.B. if `lv.i = lv.j' with `i < j' then `lv.i' and `lp.i'
          ++ are ignored.
        eval: (%, Generator(Cross(V,%))) -> %;
          ++ `eval(p,g)' evaluates `p' at `v' with `q' for `(v,q)'
          ++ in `g'. Hence the ordering on the evaluations is given
          ++ by `g'.
        if R has CommutativeRing then {
           monicDivide: (%, %, V) -> (%, %);
             ++ `monicDivide(a, b, v)' returns the `(q, r)' such that `q'
             ++ and `r' are respectively the quotient and the remainder
             ++ of the division of `a' by `b' which assumed to be monic.
             ++ w.r.t. `v'.
           differentiate: (%, V) -> %;
	     ++ `differentiate(p, v)' computes the partial derivative of
	     ++ the polynomial `p' with respect to the variable `v'.
           differentiate: (%, V, NNI) -> %;
	     ++ `differentiate(p, v, n)' computes the n-th partial derivative
	     ++ of the polynomial p with respect to the variable `v'
	   differentiate: (%, List V) -> %;
	     ++ `differentiate(p, lv)'  returns `p' if `lv' is empty otherwise 
             ++ returns `differentiate(differentiate(p,first(lv)), rest(lv))'.
	   differentiate: (%, List V, List NNI) -> %;
  	     ++ `differentiate(p, lv, ln)' returns `p' if `lv' or `ln' 
             ++ are empty otherwise returns
             ++ `differentiate(differentiate(p,lv.1,ln.1),rest lv, rest ln)'.
        }
        if V has VariableType then {
           expand: (E: ECATV) -> ((P: FAMR(R, V, E)) ->  (% -> P));
             ++ `expand(E)(P)(p)' converts the multivariate polynomial
             ++ `p' into a distributed polynomial of the domain `P'.
           combine: (E:ECATV) -> ((P: FAMR(R, V, E)) ->  (P -> %));
             ++ `combine(E)(P)(p)' converts the distributed polynomial
             ++ `p' into a multivariate polynomial in `%'.
        }
        if R has CommutativeRing then CommutativeRing;
      	if R has IntegralDomain then IntegralDomain;
	if R has GcdDomain then GcdDomain;

        default {
           import from R, V, Integer, NNI;

           degree(p: %, v: V) : NNI == {
              import from SUP(%);
              sup := univariate(SUP(%))(p,v);
              degree(sup);
           }
           eval(x: %, v: V, y: %): % == {
              import from SUP(%);
              sup := univariate(SUP(%))(x,v);
              import from GMPInteger;
              zero? degree(sup) => x;
              apply(sup,y); 
           }
           eval(x: %, v: V, r: R): % == {
              eval(x, v, r::%);
           }
           eval (p:%, lv: List V, lr: List R): % == {
              import from MachineInteger;
              assert(#lv = #lr);
              while (not empty? lv) repeat {
                 p := eval(p,first(lv),first(lr));
                 lv := rest(lv); lr := rest(lr);
              }
              p;
           }    
           local construct(lv: List V, lp: List %): Generator(Cross(V,%)) == {
              SAS ==> SortedAssociationSet(V,%);
              local sas: SAS := table()$SAS;
              while (not empty? lv) repeat {
                 lv := rest(lv); lp := rest(lp);
                 set!(sas,first(lv),first(lp));
              }
              lvp: List(Cross(V,%)) := [vp for vp in generator(sas)];
              lvp := reverse(lvp);
              generator(lvp);
           }
	   eval(x: %, lv: List V, lp: List %): % == {
              eval(x, construct(lv,lp)@Generator(Cross(V,%)));
           }
           eval(x: %, g: Generator(Cross(V,%))): % == {
              for vp in g repeat {
                  (v: V, p: %) := vp;
                  x := eval(x,v,p);
              }
              x;  
	   } 
           if R has CommutativeRing then {
              monicDivide(a: %, b: %, v: V): (%, %) == {
                  import from SUP(%);
                  supb := univariate(SUP(%))(b,v);
                  assert(not ground? supb);
                  assert(unit? leadingCoefficient(supb));
                  supa := univariate(SUP(%))(a,v);
                  (supq, supr) := monicDivide(supa,supb);
                  q := multivariate(SUP(%))(supq,v);
                  r := multivariate(SUP(%))(supr,v);
                  (q, r);
              }
              differentiate(p: %, v: V): % == {
                 import from SUP(%);
                 sup := univariate(SUP(%))(p,v);
                 sup := differentiate(sup);
                 multivariate(SUP(%))(sup,v);
              }
              differentiate (p: %, lv: List V): % == {
                 for v in lv repeat p := differentiate(p,v);
                 p;
              }   
              differentiate(p: %, lv: List V, ln: List NNI): % == {
                 import from MachineInteger;
                 assert(#lv = #ln);
                 while (not empty? lv)  repeat {
                    p := differentiate(p, first lv, first ln);
                    lv := rest lv, ln := rest ln;
                 }
                 p;
              } 
              differentiate (p: %, v: V, n: NNI): % == {
                 n = 0 => p;
                 n = 1 => differentiate(p,v);
                 import from SUP(%);
                 sup := univariate(SUP(%))(p,v);
                 sup := differentiate(sup,n);
                 multivariate(SUP(%))(sup,v);
              }
           }
           if V has VariableType then {
              expand (E:ECATV) (P:FAMR(R, V, E)) (p:%) : P == {
                 import from E, P;
                 dmp: P := 0;
                 for pair in support(p) repeat {
                     (r: R, m: %) := pair;
                     dmp := add!(dmp,term(r,degrees(m)));
                 }
                 dmp;
              }
              combine (E:ECATV) (P:FAMR(R, V, E)) (dmp:P) : % == {
                 import from E, P;
                 p: % := 0;
                 for cross in terms(dmp)@Generator(Cross(R,E)) repeat {
                     (r: R, e: E) := cross;
                     p := add!(p,term(r,terms(e)));
                 }
                 p;   
              }
           }
	   if R has GcdDomain then {
	        macro gcdpack == MultivariatePolynomialGcdPackage(R, V, %);
--              import from Generator %;		
--		gcd(gen: Generator %) : % =={
--                    g:%:=0;
--                    import from gcdpack;
--                    for pol in gen repeat {
--                           g:%:=gcd(g,pol)$gcdpack;
--                           unit? g => return 1;
--                           }
--                    return(g);}

		gcd(a: %, b: %): % == {
                    import from gcdpack;
                    gcd(a,b)$gcdpack;}
           }
           if R has FiniteCharacteristic then {
               pthPower(x: %): % == {
                  ground? x => pthPower(leadingCoefficient(x)) ::%;
                  import from SUP(%) pretend FiniteCharacteristic;
                  v: V := mainVariable(x);
                  sup := univariate(SUP(%))(x,v);
                  sup := pthPower(sup);
                  multivariate(SUP(%))(sup,v);
               }
           }
       }
}




#if ALDOC
\thistype{PolynomialRing}
\History{Marc Moreno Maza}{08/07/01}{created}
\Usage{\this~(R,V): Category}
\Params{
{\em R} & \altype{ArithmeticType} & The coefficient domain \\
        & \altype{ExpressionType} &\\
{\em V} & \altype{TotallyOrderedType} & The variable domain \\
         & \altype{ExpressionType} &\\
}
\Descr{\this~(R,V) is a category which inherits from \altype{PolynomialRing0}(R,V)
and exports some additionnal operations related to differentiation, evaluation
and polynomial type conversion.}
\begin{exports}
\category{\altype{PolynomialRing0}(R,V)} \\
\alexp{eval}: &  (\%, V, R) $\to$ \%
           &  \alexp{eval}$(x,v,r)$ evaluates $x$ at $v = r$\\
\alexp{eval}: &  (\%, V, \%) $\to$ \% 
            &  \alexp{eval}$(x,v,y)$ evaluates $x$ at $v = y$\\ 
\end{exports}
\begin{alwhere}
GEN &==& \altype{Generator}\\
PZ &==& \albuiltin{Cross}(\%, \altype{Integer})\\
\end{alwhere}
\begin{exports}[if {\em R} has \altype{CommutativeRing} then]
\alexp{differentiate}: & (\%, V) $\to$ \% 
           &  Differentiation w.r.t. a variable\\
\alexp{differentiate}: &  (\%, V, \altype{Integer}) $\to$ \% 
          &  Iterated differentiation w.r.t. a variable \\
\end{exports}
\begin{exports}[if {\em R} has \altype{CommutativeRing} then]
\category{\altype{CommutativeRing}}\\
\end{exports}
\begin{exports}[if {\em R} has \altype{IntegralDomain} then]
\category{\altype{IntegralDomain}}\\
\end{exports}
\begin{exports}[if {\em R} has \altype{GcdDomain} then]
\category{\altype{GcdDomain}}\\
\end{exports}
#endif


