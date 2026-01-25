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
# objects	  = avltree.o bintree.o bstree.o strtable.o ttable.o
# asobjects = avltree.ao bintree.ao bstree.ao strtable.ao ttable.ao
objects	  = bintree.o bstree.o
asobjects = bintree.ao bstree.ao
options   = -m2 -mno-mactext -fao -fo -q3 -csmax=0
tex       = avltree.tex bintree.tex bstree.tex strtable.tex ttable.tex
# test      = Tavltree.as Tbstree.as Tstrtable.as Tttable.as
test      =
testdir   = ../../test
libsumit  = ../../lib/libsumit.a
sumitasl  = ../../lib/libsumit.al

all: datestamp

datestamp: $(objects)
	ar rv $(libsumit) $(objects)
	touch datestamp

avltree.o: avltree.as bintree.o ../basic/nilrec.o
	axiomxl $(options) avltree.as
	ar rv $(sumitasl) avltree.ao

bintree.o: bintree.as
	axiomxl $(options) bintree.as
	ar rv $(sumitasl) bintree.ao

bstree.o: bstree.as bintree.o
	axiomxl $(options) bstree.as
	ar rv $(sumitasl) bstree.ao

strtable.o: strtable.as avltree.o ../util/stdutil.o
	axiomxl $(options) strtable.as
	ar rv $(sumitasl) strtable.ao

ttable.o: ttable.as avltree.o
	axiomxl $(options) ttable.as
	ar rv $(sumitasl) ttable.ao

.PHONY: doc
doc: $(tex)

avltree.tex: avltree.as
	as2doc avltree

bintree.tex: bintree.as
	as2doc bintree

bstree.tex: bstree.as
	as2doc bstree

strtable.tex: strtable.as
	as2doc strtable

ttable.tex: ttable.as
	as2doc ttable

.PHONY: test
test: $(test)

Tavltree.as: avltree.as
	as2test avltree
	cp Tavltree.as $(testdir)

Tbstree.as: bstree.as
	as2test bstree
	cp Tbstree.as $(testdir)

Tstrtable.as: strtable.as
	as2test strtable
	cp Tstrtable.as $(testdir)

Tttable.as: ttable.as
	as2test ttable
	cp Tttable.as $(testdir)

.PHONY: clean
clean:
	-rm $(objects) $(asobjects) $(tex) $(test)

