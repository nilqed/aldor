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
objects   = matcat0.o vect.o laring.o overdet.o
asobjects = matcat0.ao vect.ao laring.ao overdet.ao
options   = -M2 -Fao -Fo -Q3 -Csmax=0 -Mno-mactext
tex	  = matcat0.tex vect.tex laring.tex overdet.tex
test      = Tvect.as
testdir   = ../../../test
libsumit  = ../../../lib/libsumit.a
sumitasl  = ../../../lib/libsumit.al

all: datestamp

datestamp: $(objects)
	ar rv $(libsumit) $(objects)
	touch datestamp

vect.o: vect.as ../../univpoly/gcd/gcdint.o ../../extree/operators/OPvect.o
	axiomxl $(options) vect.as
	ar rv $(sumitasl) vect.ao

matcat0.o: matcat0.as vect.o
	axiomxl $(options) matcat0.as
	ar rv $(sumitasl) matcat0.ao

laring.o: laring.as matcat0.o
	axiomxl $(options) laring.as
	ar rv $(sumitasl) laring.ao

overdet.o: overdet.as matcat0.o
	axiomxl $(options) overdet.as
	ar rv $(sumitasl) overdet.ao

.PHONY: doc
doc: $(tex)

matcat0.tex: matcat0.as
	as2doc matcat0

vect.tex: vect.as
	as2doc vect

laring.tex: laring.as
	as2doc laring

overdet.tex: overdet.as
	as2doc overdet

#.PHONY: test
test: $(test)

Tvect.as: vect.as
	as2test vect
	cp Tvect.as $(testdir)

.PHONY: clean
clean:
	-rm $(objects) $(asobjects) $(tex) $(test)

