{VERSION 1 0 "X11/Motif" "1.0"}{GLOBALS 3 1}{FONT 0 "-adobe-helve
tica-bold-r-normal--*-140-*-*-*-*-*-*" "helvetica" "Helvetica-Bol
d" 8 14 0 "Helvetica-Bold" 14}{FONT 1 "-adobe-times-medium-r-norm
al--*-140-*" "times" "Times-Roman" 4 14 64 "Times-Roman" 12}{FONT
 2 "-adobe-courier-medium-r-normal--*-140-*" "courier" "Courier" 
4 14 192 "Courier" 12}{SCP_R 1 0 51{INP_R 2 0 "> "{TEXT 0 39 "lib
name := `.`, libname: with(bernina);"}}{SEP_R 3 0}{INP_R 4 0 "> "
{TEXT 0 43 "bdsolve := proc(L, D, x) local dbx, n, deg;"}}{INP_R 
5 0 "> "{TEXT 0 90 "dbx := Darboux(L, D, x, `y`); if dbx = [] the
n RETURN(dbx); fi; n := linalg[vectdim](dbx);"}}{INP_R 6 0 "> "
{TEXT 0 68 "deg := degree(dbx[1], `y`); if deg = 1 then degree1(d
bx, n, `y`, x);"}}{INP_R 7 0 "> "{TEXT 0 82 "elif deg = 2 then de
gree2(dbx[1], `y`, x); else degreen(dbx[1],  `y`, x); fi; end:"}}
{SEP_R 8 0}{INP_R 9 0 "> "{TEXT 0 97 "degree1 := proc(curves, n, \+
y, x) local i; [seq(exp(int(solve(curves[i], y), x)), i = 1..n)];
 end:"}}{SEP_R 10 0}{INP_R 11 0 "> "{TEXT 0 111 "degree2 := proc(
curve, y, x) local s, i; s := [solve(curve, y)]; [seq(exp(int(s[i
], x)), i = 1..nops(s))]; end:"}}{SEP_R 12 0}{INP_R 13 0 "> "
{TEXT 0 64 "degreen := proc(curve, y, x) exp(Int(RootOf(curve, y)
, x)); end:"}}{SEP_R 14 0}{SEP_R 15 0}{INP_R 16 0 "> "{TEXT 0 21 
"L1 := D^2 + 3/16/x^2;"}}{INP_R 17 0 "> "{TEXT 0 32 "sol1 := bdso
lve(L1, D, x); sol1;"}}{SEP_R 18 0}{INP_R 19 0 "> "{TEXT 0 30 "L2
 := (x^2-2)*D^2 + x*D - 1/4;"}}{INP_R 20 0 "> "{TEXT 0 32 "sol2 :
= bdsolve(L2, D, x); sol2;"}}{SEP_R 21 0}{INP_R 22 0 "> "{TEXT 0 
92 "L3 := D^2-2/(2*x-1)*D+(27*x^4-54*x^3+5*x^2+22*x+27)*(2*x-1)^2
/(144*x^2*(x-1)^2*(x^2-x-1)^2);"}}{INP_R 23 0 "> "{TEXT 0 32 "sol
3 := bdsolve(L3, D, x); sol3;"}}{SEP_R 24 0}{INP_R 25 0 "> "{TEXT
 0 79 "L4 := D^2-2/(2*x-1)*D+3*(2*x-1)^2*(x^4-2*x^3+x+1)/(16*x^2*
(x-1)^2*(x^2-x-1)^2);"}}{INP_R 26 0 "> "{TEXT 0 32 "sol4 := bdsol
ve(L4, D, x); sol4;"}}{SEP_R 27 0}{INP_R 28 0 "> "{TEXT 0 55 "L5 \+
:= D^2 - (-3/16/x^2 - 2/9/(x-1)^2 + 3/(16*x*(x-1)));"}}{INP_R 29 
0 "> "{TEXT 0 32 "sol5 := bdsolve(L5, D, x); sol5;"}}{SEP_R 30 0}
{SEP_R 31 0}{INP_R 32 0 "> "{TEXT 0 101 "op2deq := proc(L,D,y,x) \+
coeff(L,D,2)*diff(y(x),x$2)+coeff(L,D,1)*diff(y(x),x)+coeff(L,D,0
)*y(x); end:"}}{SEP_R 33 0}{INP_R 34 0 "> "{TEXT 0 31 "dsolve(op2
deq(L1,D,y,x), y(x));"}}{SEP_R 35 0}{INP_R 36 0 "> "{TEXT 0 37 "y
2 := dsolve(op2deq(L2,D,y,x), y(x));"}}{SEP_R 37 0}{INP_R 38 0 ">
 "{TEXT 0 37 "y3 := dsolve(op2deq(L3,D,y,x), y(x));"}}{SEP_R 39 0
}{INP_R 40 0 "> "{TEXT 0 31 "dsolve(op2deq(L4,D,y,x), y(x));"}}
{SEP_R 41 0}{INP_R 42 0 "> "{TEXT 0 31 "dsolve(op2deq(L5,D,y,x), \+
y(x));"}}{SEP_R 43 0}{INP_R 44 0 "> "{TEXT 0 100 "normal(eval(sub
s(y(x)=sol2[1],op2deq(L2,D,y,x))));normal(eval(subs(y(x)=sol2[2],
op2deq(L2,D,y,x))));"}}{SEP_R 45 0}{INP_R 46 0 "> "{TEXT 0 58 "si
mplify(eval(subs(y(x) = rhs(y2), op2deq(L2, D, y, x))));"}}{SEP_R
 47 0}{INP_R 48 0 "> "{TEXT 0 100 "normal(eval(subs(y(x)=sol3[1],
op2deq(L3,D,y,x))));normal(eval(subs(y(x)=sol3[2],op2deq(L3,D,y,x
))));"}}{SEP_R 49 0}{INP_R 50 0 "> "{TEXT 0 56 "normal(eval(subs(
y(x) = rhs(y3), op2deq(L3, D, y, x))));"}}{SEP_R 51 0}{INP_R 52 0
 "> "{TEXT 0 0 ""}}}{END}
