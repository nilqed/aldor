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
objects   = eigenring.o order2modp.o lodomod.o horder2.o order2.o
asobjects = eigenring.ao order2modp.ao lodomod.ao horder2.ao order2.ao
flags	  = -M2 -Fao -Fo -Csmax=0 -Mno-mactext
options   = $(flags) -q3
tex       = eigenring.tex order2modp.tex horder2.tex order2.tex
test      = Teigenring.as Torder2modp.as
testdir   = ../../test
libsumit  = ../../lib/libsumit.a
sumitasl  = ../../lib/libsumit.al

all: datestamp

datestamp: $(objects)
	ar rv $(libsumit) $(objects)
	touch datestamp

eigenring.o: eigenring.as ../diffeq/ratsol/sysratsol.o
	axiomxl $(options) eigenring.as
	ar rv $(sumitasl) eigenring.ao

order2modp.o: order2modp.as ../diffeq/system/lodosystem.o ../ffield/pfcat.o ../polyfactor0/zringint.o ../skewpoly/lodo/CATlodo.o
	axiomxl $(options) order2modp.as
	ar rv $(sumitasl) order2modp.ao

horder2.o: horder2.as order2modp.o lodomod.o
	axiomxl $(options) horder2.as
	ar rv $(sumitasl) horder2.ao

order2.o: order2.as horder2.o ../diffeq/ratsol/ratsol.o
	axiomxl $(options) order2.as
	ar rv $(sumitasl) order2.ao

lodomod.o: lodomod.as ../skewpoly/lodo/CATlodo.o ../categories/CATprime0.o
	axiomxl $(options) lodomod.as
	ar rv $(sumitasl) lodomod.ao

.PHONY: doc
doc: $(tex)

eigenring.tex: eigenring.as
	as2doc eigenring

order2modp.tex: order2modp.as
	as2doc order2modp

horder2.tex: horder2.as
	as2doc horder2

order2.tex: order2.as
	as2doc order2

.PHONY: test
test: $(test)

Teigenring.as: eigenring.as
	as2test eigenring
	cp Teigenring.as $(testdir)

Torder2modp.as: order2modp.as
	as2test order2modp
	cp Torder2modp.as $(testdir)

.PHONY: clean
clean:
	-rm $(objects) $(asobjects) $(tex) $(test)

