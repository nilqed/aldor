#include "axllib.as"
#pile

#library PolyCat "polycat.ao"
import from   PolyCat

macro
  NonNegativeInteger == Integer
  SmallInteger == SingleInteger
  NNI == Integer
  null xx == empty? xx
  messagePrint s == print << s << newline
  MyPolynomialCategory(S,Expon) == PolynomialCategory(S, Expon) with { primitivePart: % -> % }

GroebnerPackage(S:     EuclideanDomain, _
                Expon: ExponentCategory, _
                Dpol:  MyPolynomialCategory(S,Expon)): with

     groebner: List(Dpol) -> List(Dpol)
       ++ groebner(lp) computes a groebner basis for a polynomial ideal
       ++ generated by the list of polynomials lp.
     groebner: ( List(Dpol), String ) -> List(Dpol)
       ++ groebner(lp, infoflag) computes a groebner basis 
       ++ for a polynomial ideal
       ++ generated by the list of polynomials lp.
       ++ Argument infoflag is used to get information on the computation.
       ++ If infoflag is "info", then summary information
       ++ is displayed for each s-polynomial generated.
       ++ If infoflag is "redcrit", the reduced critical pairs are displayed.
       ++ If infoflag is any other string, no information is printed during computation.
     groebner: ( List(Dpol), String, String ) -> List(Dpol)
       ++ groebner(lp, "info", "redcrit") computes a groebner basis
       ++ for a polynomial ideal generated by the list of polynomials lp,
       ++ displaying both a summary of the critical pairs considered ("info")
       ++ and the result of reducing each critical pair ("redcrit").
       ++ If the second or third arguments have any other string value,
       ++ the indicated information is suppressed.
       
--     if Dom has Field then
     normalForm: (Dpol, List(Dpol))  -> Dpol
          ++ normalForm(poly,gb) reduces the polynomial poly modulo the
          ++ precomputed groebner basis gb giving a canonical representative
          ++ of the residue class.


 == add
      import from Dpol, Expon, S, ListSort(Dpol)
      import from GroebnerInternalPackage(S,Expon,Dpol)
      normalForm: (Dpol,List Dpol) -> Dpol 
      normalForm(p:Dpol,l:List Dpol):Dpol ==
        redPol(p,l)$GroebnerInternalPackage(S,Expon,Dpol)

      degreeOrder(p1: Dpol, p2: Dpol): Boolean == degree p2 < degree p1

      groebner (Pol:List Dpol):List Dpol ==
        import from Boolean, Integer
        Pol = [] => Pol
        Pol := [x for x in Pol | not (x = 0)]
        Pol = [] => [0]
        minGbasis sort(degreeOrder, gbasis(Pol,0,0))

      groebner(Pol:List Dpol,xx1:String):List Dpol ==
        import from Boolean, Integer
        Pol = [] => Pol
        Pol := [x for x in Pol | not (x = 0)]
        Pol = [] => [0]
        xx1 = "redcrit" =>
          minGbasis sort(degreeOrder, gbasis(Pol,1,0))
        xx1 = "info" =>
          minGbasis sort(degreeOrder, gbasis(Pol,2,1))
        messagePrint "   "
        messagePrint "WARNING: options are - redcrit and/or info - "
        messagePrint "         you didn't type them correct"
        messagePrint "         please try again"
        messagePrint "   "
        []
      groebner(Pol:List Dpol,xx1:String,xx2:String):List Dpol ==
        import from Boolean, Integer
        Pol = [] => Pol
        Pol := [x for x in Pol | not (x = 0)]
        Pol = [] => [0]
        xx1 = "redcrit" and xx2 = "info" or xx1 = "info" and xx2 = "redcrit" =>
          minGbasis sort(degreeOrder, gbasis(Pol,1,1))
        xx1 = "redcrit" and xx2 = "redcrit" =>
          minGbasis sort(degreeOrder, gbasis(Pol,1,0))
        xx1 = "info" and xx2 = "info" =>
          minGbasis sort(degreeOrder, gbasis(Pol,2,1))
        messagePrint "   "
        messagePrint "WARNING:  options are - redcrit and/or info - "
        messagePrint "          you didn't type them correctly"
        messagePrint "          please try again "
        messagePrint "   "
        []

--critPair ==> Record( lcmfij: Expon, totdeg: NonNegativeInteger,
--                      poli: Dpol, polj: Dpol )

critPair(Expon: BasicType, Dpol: BasicType): BasicType with
   bracket: (Expon, NNI, Dpol, Dpol) -> %
   apply: (%, 'lcmfij') -> Expon
   apply: (%, 'totdeg') -> NNI
   apply: (%, 'poli') -> Dpol
   apply: (%, 'polj') -> Dpol
 == add
   Rep ==>  Record( lcmfij: Expon, totdeg: NonNegativeInteger,
                      poli: Dpol, polj: Dpol )
   import from Rep
   sample: % == nil$Pointer pretend %	--!!
   (c1:%) = (c2:%):Boolean ==
     rep(c1).lcmfij = rep(c2).lcmfij and
      rep(c1).poli = rep(c2).poli and rep(c1).polj = rep(c2).polj
   (c1:%) ~= (c2:%):Boolean == not(c1=c2)
   apply(c:%, tag:'lcmfij'):Expon == rep(c).lcmfij
   apply(c:%, tag:'totdeg'):NNI   == rep(c).totdeg
   apply(c:%, tag:'poli'):Dpol    == rep(c).poli
   apply(c:%, tag:'polj'):Dpol    == rep(c).polj
   [e:Expon, d:NNI, p1:Dpol, p2:Dpol]:% == per [e,d,p1,p2]
   (p: TextWriter) << (c: %): TextWriter ==
      import from String
      p << "(" << rep(c).poli << "," << rep(c).polj << ")"

--sugarPol ==> Record( totdeg: NonNegativeInteger, pol : Dpol)

sugarPol(Dpol: BasicType): BasicType with
   bracket: (NNI, Dpol) -> %
   apply: (%, 'totdeg') -> NNI
   apply: (%, 'pol') -> Dpol
 == add
   Rep ==> Record( totdeg: NonNegativeInteger, pol : Dpol)
   import from Rep
   sample: % == nil$Pointer pretend %	--!!
   (p1:%) =  (p2:%):Boolean == rep(p1).pol = rep(p2).pol
   (p1:%) ~= (p2:%):Boolean == not(p1=p2)
   apply(p:%, tag:'totdeg'):NNI   == rep(p).totdeg
   apply(p:%, tag:'pol'):Dpol     == rep(p).pol
   [deg:NNI, p:Dpol]:%                       == per [deg,p]
   (p: TextWriter) << (spol: %): TextWriter ==
       p << rep(spol).pol


Prinp    ==> Record( ci:Dpol,tci:Integer,cj:Dpol,tcj:Integer,c:Dpol,
                tc:Integer,rc:Dpol,trc:Integer,tF:Integer,tD:Integer)
Prinpp   ==> Record( ci:Dpol,tci:Integer,cj:Dpol,tcj:Integer,c:Dpol,
                tc:Integer,rc:Dpol,trc:Integer,tF:Integer,tDD:Integer,
                 tDF:Integer)

GroebnerInternalPackage( _
	S:     EuclideanDomain, _
	Expon: ExponentCategory, _
	Dpol:  MyPolynomialCategory(S,Expon)): with
           
     redPol:   (Dpol, List(Dpol))  -> Dpol
     gbasis:  (List(Dpol), Integer, Integer) -> List(Dpol)
     minGbasis: List(Dpol) -> List(Dpol)

  == add

      import from Dpol, Expon, S
      totalDegree(p: Dpol) : SingleInteger ==
         p = 0 => 0
         max(sum(degree p), totalDegree(reductum p))
--    printPrinp(r: Prinp): TextWriter ==
--       import from String, Integer
--       print."(ci= #1,tci= #2,cj= #3,tcj= #4," (<<r.ci,<<r.tci,<<r.cj,<<r.tcj)
--       print."c= #1,tc= #2,rc= #3,trc =#4,"    (<<r.c, <<r.tc, <<r.rc,<<r.trc)
--       print."EtF= #a,tD= #a)#n"               (<<r.tF,<<r.tD)
      printPrinp(r : Prinp): TextWriter ==
         import from String, Integer
         print<<"(ci= "<<r.ci<<",tci= "<<r.tci<<",cj= "<<r.cj<<",tcj= "<<r.tcj
         print<<",c= "<<r.c<<",tc= "<<r.tc<<",rc= "<<r.rc<<",trc ="<<r.trc<<",tF= "<<r.tF
         print<<",tD= "<<r.tD<<")"
	 print<<newline
      printPrinpp(r: Prinpp):TextWriter ==
         import from String, Integer
         print<<"(ci= "<<r.ci<<",tci= "<<r.tci<<",cj= "<<r.cj<<",tcj= "<<r.tcj
         print<<",c= "<<r.c<<",tc= "<<r.tc<<",rc= "<<r.rc<<",trc ="<<r.trc<<",tF= "<<r.tF
         print<<",tDD= "<<r.tDD<<",tDF= "<<r.tDF<<")"
	 print<<newline
      import from ListSort(Dpol)
--      if Dpol has totalDegree: Dpol -> NonNegativeInteger then
      virtualDegree (p:Dpol):NonNegativeInteger == (totalDegree p)::NonNegativeInteger
--      else
--         virtualDegree (p:Dpol):NonNegativeInteger == 0
      critpOrder(cp1:critPair(Expon, Dpol),cp2:critPair(Expon, Dpol)):Boolean ==
        import from NonNegativeInteger, 'totdeg', 'lcmfij'
        cp1 totdeg < cp2 totdeg => true
        cp2 totdeg < cp1 totdeg => false
        cp1 lcmfij < cp2 lcmfij
      makeCrit(sp1:sugarPol(Dpol),p2:Dpol,totdeg2:NonNegativeInteger):critPair(Expon, Dpol) ==
        import from 'pol', 'totdeg'
        p1 := sp1 pol
        deg := sup(degree p1,degree p2)
        e1 := deg - degree p1
        e2 := deg - degree p2
        tdeg :=
          max(sp1 totdeg + virtualDegree monomial(1,e1),totdeg2 +
            virtualDegree monomial(1,e2))
        [deg,tdeg,p1,p2]$critPair(Expon, Dpol)
      gbasis(Pol:List Dpol,xx1:Integer,xx2:Integer):List Dpol ==
        import from Boolean, NonNegativeInteger
        import from ListSort critPair(Expon, Dpol), List sugarPol(Dpol)
        default D,D1:List critPair(Expon, Dpol)
        Pol1 := sort(((%1:Dpol,%2:Dpol):Boolean) +-> degree %2 < degree %1,Pol)
        Pol1 := Pol
        basPols := updatF(hMonic first Pol1,virtualDegree first Pol1,[])
        Pol1 := rest Pol1
        D := nil
        while not(null Pol1) repeat
          h:Dpol := hMonic first Pol1
          Pol1 := rest Pol1
          toth := virtualDegree h
          D1 := [makeCrit(x,h,toth) for x in basPols]
          D := updatD(critMTonD1 sort(critpOrder,D1),critBonD(h,D))
          basPols := updatF(h,toth,basPols)
        D := sort(critpOrder,D)
        xx := xx2
        import from sugarPol(Dpol), 'pol', 'totdeg', critPair(Expon, Dpol)
        redPols := [x pol for x in basPols]
        while not(null D) repeat
          D0 := first D
          s := hMonic sPol D0
          D := rest D
          h:Dpol := hMonic redPol(s,redPols)
          if xx1 = 1 then prinshINFO h
          h = 0 =>
            if xx2 = 1 then
              prindINFO(D0,s,h,#basPols::Integer,#D::Integer,xx)
              xx := 2
            " go to top of while "
          degree h = 0 =>
            D := nil
            if xx2 = 1 then
              prindINFO(D0,s,h,#basPols::Integer,#D::Integer,xx)
              xx := 2
            basPols := updatF(h,0,[])
            break
          D1 := [makeCrit(x,h,D0 totdeg) for x in basPols]
          D := updatD(critMTonD1 sort(critpOrder,D1),critBonD(h,D))
          basPols := updatF(h,D0 totdeg,basPols)
          redPols := concat(redPols,[h])
          xx2 = 1 =>
            prindINFO(D0,s,h,#basPols::Integer,#D::Integer,xx)
            xx := 2
        Pol := [x pol for x in basPols]
        if xx2 = 1 then
          prinpolINFO Pol
          messagePrint "    THE GROEBNER BASIS POLYNOMIALS"
        if xx1 = 1 and not (xx2 = 1) then
          messagePrint "    THE GROEBNER BASIS POLYNOMIALS"
        Pol
      critMonD1(e:Expon,D2:List critPair(Expon, Dpol)):List critPair(Expon, Dpol) ==
        import from critPair(Expon, Dpol), 'lcmfij'
        null D2 => nil
        x := first D2
        critM(e,x lcmfij) => critMonD1(e,rest D2)
        cons(x,critMonD1(e,rest D2))
      critMTonD1 (D1:List critPair(Expon, Dpol)):List critPair(Expon, Dpol) ==
        import from NonNegativeInteger, Boolean, critPair(Expon, Dpol), 'lcmfij'
        null D1 => nil
        f1 := first D1
        s1 := #D1 :: Integer
        cT1 := critT f1
        s1 = 1 and cT1 => nil
        s1 = 1 => D1
        e1 := f1 lcmfij
        r1 := rest D1
        e1 = (first r1).lcmfij =>
          cT1 => critMTonD1 cons(f1,rest r1)
          critMTonD1 r1
        D1 := critMonD1(e1,r1)
        cT1 => critMTonD1 D1
        cons(f1,critMTonD1 D1)
      critBonD(h:Dpol,D:List critPair(Expon, Dpol)):List critPair(Expon, Dpol) ==
	import from critPair(Expon, Dpol), 'lcmfij', 'poli', 'polj'
        null D => nil
        x := first D
        critB(degree h,x lcmfij,degree x poli,degree x polj) =>
          critBonD(h,rest D)
        cons(x,critBonD(h,rest D))
      updatF(h:Dpol,deg:NNI,F:List sugarPol(Dpol)):List sugarPol(Dpol) ==
	import from sugarPol(Dpol), 'pol'
        null F => [[deg,h]]
        f1 := first F
        critM(degree h,degree f1 pol) => updatF(h,deg,rest F)
        cons(f1,updatF(h,deg,rest F))
      updatD(D1:List critPair(Expon, Dpol),D2:List critPair(Expon, Dpol)):List critPair(Expon, Dpol) ==
        null D1 => D2
        null D2 => D1
        dl1 := first D1
        dl2 := first D2
        critpOrder(dl1,dl2) => cons(dl1,updatD(rest D1,D2))
        cons(dl2,updatD(D1,rest D2))
      gcdCo(c1:S,c2:S):Record(co1:S,co2:S) ==
        d := gcd(c1,c2)
        [c1 quo d, c2 quo d]
      sPol (p:critPair(Expon, Dpol)):Dpol ==
        import from 'lcmfij', 'poli', 'polj'
        Tij := p lcmfij
        fi := p poli
        fj := p polj
        cc := gcdCo(leadingCoefficient fi,leadingCoefficient fj)
        import from Record(co1:S,co2:S)
        reductum fi * monomial(cc co2,Tij - degree fi) - reductum fj *
          monomial(cc co1,Tij - degree fj)
      redPo(s:Dpol,F:List Dpol):Record(poly:Dpol,mult:S) ==
        import from Boolean
        m:S := 1
        Fh := F
        while not(s = 0 or null F) repeat
          f1 := first F
          s1 := degree s
          nonNegative?(e := s1 - degree f1) =>
            cc := gcdCo(leadingCoefficient f1,leadingCoefficient s)
            import from Record(co1:S,co2:S)
            s := cc co1 * reductum s - monomial(cc co2,e) * reductum f1
            m := m * cc co1
            F := Fh
          F := rest F
        [s,m]
      redPol(s:Dpol,F:List Dpol):Dpol ==
        import from Record(poly:Dpol,mult:S)
        credPol((redPo(s,F)).poly,F)
      critT (p:critPair(Expon, Dpol)):Boolean ==
        import from 'lcmfij', 'poli', 'polj'
        p lcmfij = degree p poli + degree p polj
      critM(e1:Expon,e2:Expon):Boolean ==
        nonNegative?(e2 - e1)
      critB(eh:Expon,eik:Expon,ei:Expon,ek:Expon):Boolean ==
        critM(eh,eik) and not (eik = sup(eh,ei)) and not (eik = sup(eh,ek))
      hMonic (p:Dpol):Dpol == primitivePart p
      credPol(h:Dpol,F:List Dpol):Dpol ==
        import from Boolean
        null F => h
        h0:Dpol := monomial(leadingCoefficient h,degree h)
        while not ((h := reductum h) = 0) repeat
          hred := redPo(h,F)
          import from Record(poly:Dpol,mult:S)
          h := hred poly
          h0 := hred mult * h0 + monomial(leadingCoefficient h,degree h)
        h0
      minGbasis (F:List Dpol):List Dpol ==
        null F => nil
        newbas := minGbasis rest F
        cons(hMonic credPol(first F,newbas),newbas)
      lepol (p1:Dpol):Integer ==
        import from Boolean
        n:Integer := 0
        while not (p1 = 0) repeat
          n := n + 1
          p1 := reductum p1
        n
      prinb (n:Integer): () ==
        import from SmallInteger, NonNegativeInteger, Segment Integer
        for x in 1..n repeat messagePrint "    "
      prinshINFO (hh:Dpol): () ==
        import from Integer
        prinb 2
        messagePrint " reduced Critpair - Polynom :"
        prinb 2
        print<<hh<<newline
        prinb 2
      prindINFO(cp:critPair(Expon, Dpol),ps:Dpol,ph:Dpol,i1:Integer,i2:Integer,n:Integer): Integer  ==
            import from NonNegativeInteger, 'poli', 'polj'
            default a:S
            default ll:Prinp
            cpi := cp poli
            cpj := cp polj
            if n = 1 then
              prinb 1
              messagePrint "you choose option  -info-  "
              messagePrint "abbrev. for the following information strings are"
              messagePrint.
                "  ci  =>  Leading monomial  for critpair calculation"
              messagePrint "  tci =>  Number of terms of polynomial i"
              messagePrint.
                "  cj  =>  Leading monomial  for critpair calculation"
              messagePrint "  tcj =>  Number of terms of polynomial j"
              messagePrint "  c   =>  Leading monomial of critpair polynomial"
              messagePrint "  tc  =>  Number of terms of critpair polynomial"
              messagePrint.
                "  rc  =>  Leading monomial of redcritpair polynomial"
              messagePrint "  trc =>  Number of terms of redcritpair polynomial"
              messagePrint "  tF  =>  Number of polynomials in reduction list F"
              messagePrint "  tD  =>  Number of critpairs still to do"
              prinb 4
              n := 2
            prinb 1
            a := 1
            ph = 0 =>
              ps = 0 =>
                ll :=
                  [monomial(a,degree(cpi)),lepol(cpi),monomial(a,degree(cpj)),
                    lepol(cpj),ps,0,ph,0,i1,i2]$Prinp
                printPrinp ll
                prinb 1
                n
              ll :=
                [monomial(a,degree(cpi)),lepol(cpi),monomial(a,degree(cpj)),
                  lepol(cpj),monomial(a,degree(ps)),lepol(ps),ph,0,i1,i2]$Prinp
              printPrinp ll
              prinb 1
              n
            ll :=
              [monomial(a,degree(cpi)),lepol(cpi),monomial(a,degree(cpj)),
                lepol(cpj),monomial(a,degree(ps)),lepol(ps),
                  monomial(a,degree(ph)),lepol(ph),i1,i2]$Prinp
            printPrinp ll
            prinb 1
            n
      prinpolINFO (pl:List Dpol): () ==
        import from Integer
        n:Integer := (#pl)::Integer
        prinb 1
        n = 1 =>
          messagePrint "  There is 1  Groebner Basis Polynomial "
          prinb 2
        messagePrint "  There are "
        prinb 1
        print << n
        prinb 1
        messagePrint "  Groebner Basis Polynomials. "
        prinb 2
      fprindINFO(cp:critPair(Expon, Dpol),ps:Dpol,ph:Dpol,i1:Integer,_
        i2:Integer,i3:Integer,n:Integer):Integer ==
            import from NonNegativeInteger, 'poli', 'polj'
            default ll:Prinpp
            default a:S
            cpi := cp poli
            cpj := cp polj
            if n = 1 then
              prinb 1
              messagePrint "you choose option  -info-  "
              messagePrint "abbrev. for the following information strings are"
              messagePrint.
                "  ci  =>  Leading monomial  for critpair calculation"
              messagePrint "  tci =>  Number of terms of polynomial i"
              messagePrint.
                "  cj  =>  Leading monomial  for critpair calculation"
              messagePrint "  tcj =>  Number of terms of polynomial j"
              messagePrint "  c   =>  Leading monomial of critpair polynomial"
              messagePrint "  tc  =>  Number of terms of critpair polynomial"
              messagePrint.
                "  rc  =>  Leading monomial of redcritpair polynomial"
              messagePrint "  trc =>  Number of terms of redcritpair polynomial"
              messagePrint "  tF  =>  Number of polynomials in reduction list F"
              messagePrint "  tD  =>  Number of critpairs still to do"
              messagePrint "  tDF =>  Number of subproblems still to do"
              prinb 4
              n := 2
            prinb 1
            a := 1
            ph = 0 =>
              ps = 0 =>
                ll :=
                  [monomial(a,degree(cpi)),lepol(cpi),monomial(a,degree(cpj)),
                    lepol(cpj),ps,0,ph,0,i1,i2,i3]$Prinpp
                printPrinpp ll
                prinb 1
                n
              ll :=
                [monomial(a,degree(cpi)),lepol(cpi),monomial(a,degree(cpj)),
                  lepol(cpj),monomial(a,degree(ps)),lepol(ps),ph,0,i1,i2,i3]$Prinpp
              printPrinpp ll
              prinb 1
              n
            ll :=
              [monomial(a,degree(cpi)),lepol(cpi),monomial(a,degree(cpj)),
                lepol(cpj),monomial(a,degree(ps)),lepol(ps),
                  monomial(a,degree(ph)),lepol(ph),i1,i2,i3]$Prinpp
            printPrinpp ll
            prinb 1
            n