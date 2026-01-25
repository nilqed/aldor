{VERSION 1 0 "X11/Motif" "1.0"}{GLOBALS 3 1}{FONT 0 "-adobe-helve
tica-bold-r-normal--*-140-*" "helvetica" "Helvetica-Bold" 8 14 0 
"Helvetica-Bold" 12}{FONT 1 "-adobe-times-medium-r-normal--*-140-
*" "times" "Times-Roman" 4 14 64 "Times-Roman" 12}{FONT 2 "-adobe
-courier-medium-r-normal--*-140-*" "courier" "Courier" 4 14 192 "
Courier" 12}{SCP_R 1 0 60{INP_R 2 0 "> "{TEXT 0 38 "libname := `.
`,libname: with(bernina);"}}{OUT_R 3 0 2{DAG [2,7n4\`Darboux`n4\`
adjoint`n4\`apply`n4\`kernel`n6\`symmetricKernel`n6\`symmetricPow
er`}}{INP_R 4 0 "> "{TEXT 0 26 "L := (x^2-2)^2 *D^2 + 3/2;"}}
{OUT_R 5 0 4{DAG :3n3\`L`+5*5+5*3n3\`x`j2x0002j2x0001i2x0002pBp9n
3\`D`p9pB/3j2x0003p9pB}}{SEP_R 6 0}{INP_R 7 0 "> "{TEXT 0 32 "C :
= Darboux(L,D,x,y); print(C);"}}{OUT_R 8 0 7{DAG (3n4\`VECTOR`,2[
2,2+9*5+7*3n3\`x`j2x0004j2x0001*3pBj2x0002i2x0004pDpFpFn3\`y`p13p
F*5+5*3pBj2x0003i2x0002pBpDpFp1ApFpFp11pF/3i2x0001p13pF}}{SEP_R 9
 0}{INP_R 10 0 "> "{TEXT 0 36 "cc1 := collect(2 * C[1], y, factor
);"}}{OUT_R 11 0 10{DAG :3n3\`cc1`+9*5+5*3n3\`x`j2x0002j2x0001i2x
0002pBp9n3\`y`p9p9*7p7pBp5pBp11pBi2x0004p6p9i2x0001pB}}{SEP_R 12 
0}{INP_R 13 0 "> "{TEXT 0 34 "L2 := symmetricPower(L,D,x,2); L2;"
}}{OUT_R 14 0 13{DAG +7*5+9*3n3\`x`j2x0006j2x0001*3p4j2x0004i2x00
06*3p4j2x0002j2x0012i2x0008p8p8n3\`D`j2x0003p8*5+5p10p6i2x0012p8p
8p1Ap8p8p4p23}}{SEP_R 15 0}{INP_R 16 0 "> "{TEXT 0 30 "V := kerne
l(L2,D,x); print(V);"}}{OUT_R 17 0 16{DAG (3n4\`VECTOR`,2[2,2+5*3
n3\`x`j2x0002j2x0001i2x0002pD}}{SEP_R 18 0}{INP_R 19 0 "> "{TEXT 
0 65 "ric := proc(u,x) normal((x^2-2)^2 * (diff(u,x) + u^2) + 3/2
) end;"}}{OUT_R 20 0 19{DAG :3n3\`ric`@8,3n3\`u`n3\`x`,1p9p9(3n4\
`normal`,2+5*5+5*3a2x0002j2x0002j2x0001i2x0002p19p17+5(3n4\`diff`
,3a2x0001p15p19*3p25p17p19p19p19/3j2x0003p17p19p9p9}{TEXT 2 60 "\
012ric := proc(u,x) normal((x^2-2)^2*(diff(u,x)+u^2)+3/2) end\012
"}}{SEP_R 21 0}{INP_R 22 0 "> "{TEXT 0 22 "s1 := [solve(cc1, y)];
"}}{OUT_R 23 0 22{DAG :3n3\`s1`[2,3+3*5+7*3n3\`x`j2x0004j2x0002*3
p9pDi2x0008j2x0008j2x0001i2x0001+7*3p9j2x0003pBp9p12*5pD/3p16pD+5
pFp16i2x0002p16p16pDp16p24+3*5p7p18+7p1BpBp9p12p22p2Ap16p24}}
{SEP_R 24 0}{INP_R 25 0 "> "{TEXT 0 28 "ric(s1[1],x); ric(s1[2], \+
x);"}}{OUT_R 26 0 25{DAG j2x0000}}{OUT_R 27 0 25{DAG j2x0000}}
{SEP_R 28 0}{INP_R 29 0 "> "{TEXT 0 45 "cc2 := 2*(x^2-2)^2 * y^2 \+
- 2*x*(x^2-2)*y + 1;"}}{OUT_R 30 0 29{DAG :3n3\`cc2`+7*5+5*3n3\`x
`j2x0002j2x0001i2x0002pBp9n3\`y`p9p9*7p7pBp5pBp11pBpDpBpB}}{SEP_R
 31 0}{INP_R 32 0 "> "{TEXT 0 67 "cc3 := 2*x*(x^2-2)^2*y^2 - 4*(x
-1)*(x+1)*(x^2-2)*y + x*(2*x^2 - 3);"}}{OUT_R 33 0 32{DAG :3n3\`c
c3`+7*7n3\`x`j2x0001+5*3p5j2x0002p7i2x0002p7pCn3\`y`pCpC*9+5p5p7i
2x0001p7p7+5p5p7p7p7p7p9p7p13p7i2x0004*5p5p7+5pApCi2x0003p7p7p7}}
{SEP_R 34 0}{INP_R 35 0 "> "{TEXT 0 44 "s2 := [solve(cc2,y)]; s3 \+
:= [solve(cc3, y)];"}}{OUT_R 36 0 35{DAG :3n3\`s2`[2,3+3*5+7*3n3\
`x`j2x0004j2x0002*3p9pDi2x0008j2x0008j2x0001i2x0001+7*3p9j2x0003p
Dp9i2x0004*3+9*3p9j2x0006p16p8i2x0006pFj2x0012p12p16/3p16pDpDp16p
32+3*5p7p18+7p1BpDp9p21p23i2x0002p16p32}}{OUT_R 37 0 35{DAG :3n3\
`s3`[2,3+3*5+7*3n3\`x`j2x0005j2x0002*3p9j2x0003i2x0008p9j2x0008i2
x0001+9*3p9j2x0004p1D*3p9pDi2x0012p16j2x0001*3+9*3p9j2x0006i2x000
2p1Bj2x0012p20i2x0024j2x0016p26/3p26pDpDp26p39+3*5p7p18+9p1Bp1Dp2
0p23p16p26p28p2Ep26p39}}{SEP_R 38 0}{INP_R 39 0 "> "{TEXT 0 56 "r
ic(s2[1],x); ric(s2[2],x); ric(s3[1],x); ric(s3[2], x);"}}{OUT_R 
40 0 39{DAG j2x0000}}{OUT_R 41 0 39{DAG j2x0000}}{OUT_R 42 0 39
{DAG j2x0000}}{OUT_R 43 0 39{DAG j2x0000}}{SEP_R 44 0}{INP_R 45 0
 "> "{TEXT 0 42 "gcd(cc1, cc2); gcd(cc1,cc3); gcd(cc2,cc3);"}}
{OUT_R 46 0 45{DAG j2x0001}}{OUT_R 47 0 45{DAG j2x0001}}{OUT_R 48
 0 45{DAG j2x0001}}{SEP_R 49 0}{INP_R 50 0 "> "{TEXT 0 59 "cf := \+
proc(c, y) normal(- coeff(c,y,1) / coeff(c,y,2)) end;"}}{OUT_R 51
 0 50{DAG :3n3\`cf`@8,3n3\`c`n3\`y`,1p9p9(3n4\`normal`,2+3*5(3n4\
`coeff`,4a2x0001a2x0002j2x0001p1C(3p14,4p18p1Aj2x0002i2x0001p26p9
p9}{TEXT 2 56 "\012cf := proc(c,y) normal(-coeff(c,y,1)/coeff(c,y
,2)) end\012"}}{SEP_R 52 0}{INP_R 53 0 "> "{TEXT 0 32 "cf(cc1,y);
 cf(cc2,y); cf(cc3,y);"}}{OUT_R 54 0 53{DAG +3*5n3\`x`j2x0001+5*3
p2j2x0002p4i2x0002p4i2x0001p9}}{OUT_R 55 0 53{DAG *5n3\`x`j2x0001
+5*3p1j2x0002p3i2x0002p3i2x0001}}{OUT_R 56 0 53{DAG +3*9+5n3\`x`j
2x0001i2x0001p5p5+5p3p5p5p5p5+5*3p3j2x0002p5i2x0002p5p7p3p7p14}}
{SEP_R 57 0}{INP_R 58 0 "> "{TEXT 0 18 "diff(V[1],x)/V[1];"}}
{OUT_R 59 0 58{DAG +3*5n3\`x`j2x0001+5*3p2j2x0002p4i2x0002p4i2x00
01p9}}{SEP_R 60 0}{INP_R 61 0 "> "{TEXT 0 0 ""}}}{END}
