@ECHO OFF

aldor -csmax=0 -q5 -qinline-all -fo -fao multlodo.as
aldor -csmax=0 -q5 -qinline-all -fo -fao evalodo.as
aldor -fx -csmax=0 -q5 -qinline-all -lsumit -lalgebra -laldor bernina.as multlodo.obj evalodo.obj


