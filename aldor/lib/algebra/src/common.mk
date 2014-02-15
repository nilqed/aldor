aldorincdir	:= $(top_srcdir)/lib/aldor/include
aldorlibdir	:= $(top_builddir)/lib/aldor/src

libraryname	:= algebra
librarydeps     := aldor

#AXLCDB		:= -W check -Csmax=0 -Zdb -Qno-cc
AXLFLAGS	:= -Z db -Q2 $(AXLCDB)
AXLFLAGS	+= -Y $(aldorlibdir) -I $(aldorincdir) -laldor

include $(top_srcdir)/lib/buildlib.mk
