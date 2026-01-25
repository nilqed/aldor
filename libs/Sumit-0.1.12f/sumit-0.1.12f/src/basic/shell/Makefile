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
objects   = symtable.o partring.o makepring.o evaluator.o shell.o
asobjects = symtable.ao partring.ao makepring.ao evaluator.ao shell.ao
options   = -M2 -Fao -Fo -Q3 -Csmax=0 -Mno-mactext
tex	  = 
tex	  = symtable.tex partring.tex makepring.tex evaluator.tex shell.tex
test      =
testdir   = ../../../test
libsumit  = ../../../lib/libsumit.a
sumitasl  = ../../../lib/libsumit.al

all: datestamp

datestamp: $(objects)
	ar rv $(libsumit) $(objects)
	touch datestamp

symtable.o: symtable.as
	axiomxl $(options) symtable.as
	ar rv $(sumitasl) symtable.ao

partring.o: partring.as ../../categories/CATbasic.o
	axiomxl $(options) partring.as
	ar rv $(sumitasl) partring.ao

makepring.o: makepring.as partring.o ../../categories/CATfield.o
	axiomxl $(options) makepring.as
	ar rv $(sumitasl) makepring.ao

evaluator.o: evaluator.as partring.o symtable.o
	axiomxl $(options) evaluator.as
	ar rv $(sumitasl) evaluator.ao

shell.o: shell.as evaluator.o ../../extree/parser/parser.o
	axiomxl $(options) shell.as
	ar rv $(sumitasl) shell.ao

.PHONY: doc
doc: $(tex)

symtable.tex: symtable.as
	as2doc symtable

partring.tex: partring.as
	as2doc partring

makepring.tex: makepring.as
	as2doc makepring

evaluator.tex: evaluator.as
	as2doc evaluator

shell.tex: shell.as
	as2doc shell

.PHONY: clean
clean:
	-rm $(objects) $(asobjects) $(tex) $(test)

