# ======================================================================
# This code was written all or part by Dr. Manuel Bronstein from
# Inria-CAFE project team. After his sudden death on June 6, 2005, Inria
# decided to publish this code under the CeCILL open source license in
# memory of Dr. Manuel Bronstein.
# 
# This software is governed by the CeCILL license under French law and
# abiding by the rules of distribution of free software. You can use,
# modify and/or redistribute the software under the terms of the CeCILL
# license as circulated by CEA, CNRS and Inria at the following URL :
# http://www.cecill.info/licences/Licence_CeCILL_V2-en.html
# 
# As a counterpart to the access to the source code and rights to copy,
# modify and redistribute granted by the license, users are provided
# only with a limited warranty and the software's author, the holder of
# the economic rights, and the successive licensors have only limited
# liability.
# 
# In this respect, the user's attention is drawn to the risks associated
# with loading, using, modifying and/or developing or reproducing the
# software by the user in light of its specific status of free software,
# that may mean that it is complicated to manipulate, and that also
# therefore means that it is reserved for developers and experienced
# professionals having in-depth computer knowledge. Users are therefore
# encouraged to load and test the software's suitability as regards
# their requirements in conditions enabling the security of their
# systems and/or data to be ensured and, more generally, to use and
# operate it in the same conditions as regards security.
# 
# The fact that you are presently reading this means that you have had
# knowledge of the CeCILL license and that you accept its terms.
# ======================================================================
# 
objects   = place.o dplace.o lodnewton.o ratplace.o infplace.o affplace.o
asobjects = place.ao dplace.ao lodnewton.ao ratplace.ao infplace.ao affplace.ao
options	  = -M2 -Fao -Fo -Q3 -Csmax=0 -Mno-mactext
tex       = place.tex dplace.tex lodnewton.tex ratplace.tex infplace.tex affplace.tex
test      = Tratplace.as Tlodnewton.as
testdir   = ../../../test
libsumit  = ../../../lib/libsumit.a
sumitasl  = ../../../lib/libsumit.al

all: datestamp

datestamp: $(objects)
	ar rv $(libsumit) $(objects)
	touch datestamp

place.o: place.as ../../polyfactor0/zringint.o ../../univpoly/categories/upolycat.o
	axiomxl $(options) place.as
	ar rv $(sumitasl) place.ao

dplace.o: dplace.as place.o ../../diff/derivation.o
	axiomxl $(options) dplace.as
	ar rv $(sumitasl) dplace.ao

lodnewton.o: lodnewton.as place.o ../../univpoly/upoch.o ../../skewpoly/lodo/CATlodo.o
	axiomxl $(options) lodnewton.as
	ar rv $(sumitasl) lodnewton.ao

ratplace.o: ratplace.as dplace.o ../../univpoly/categories/upolycat.o ../../fraction/quotient.o ../../fraction/quotientby.o
	axiomxl $(options) ratplace.as
	ar rv $(sumitasl) ratplace.ao

infplace.o: infplace.as dplace.o ../../univpoly/categories/upolycat.o ../../fraction/quotient.o
	axiomxl $(options) infplace.as
	ar rv $(sumitasl) infplace.ao

affplace.o: affplace.as dplace.o ../../univpoly/categories/upolycat.o ../../algext/upmod.o ../../fraction/quotcat.o
	axiomxl $(options) affplace.as
	ar rv $(sumitasl) affplace.ao

.PHONY: doc
doc: $(tex)

place.tex: place.as
	as2doc place

dplace.tex: dplace.as
	as2doc dplace

lodnewton.tex: lodnewton.as
	as2doc lodnewton

ratplace.tex: ratplace.as
	as2doc ratplace

infplace.tex: infplace.as
	as2doc infplace

affplace.tex: affplace.as
	as2doc affplace

.PHONY: test
test: $(test)

Tratplace.as: ratplace.as
	as2test ratplace
	cp Tratplace.as $(testdir)

Tlodnewton.as: lodnewton.as
	as2test lodnewton
	cp Tlodnewton.as $(testdir)

.PHONY: clean
clean:
	-rm $(objects) $(asobjects) $(tex) $(test)

