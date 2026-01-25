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
all: dvi 

dvi: shasta.dvi
ps: shasta.ps
pdf: shasta.pdf
html: html/html.html

shasta.ps: shasta.dvi mountshasta.eps
	dvips shasta -o

shasta.dvi:  shasta.tex intro.tex io.tex macros.tex maple.tex ref.tex\
		 title.tex multlodo.tex
	rm -f *.aux *.ind *.idx *.toc *.ilg
	latex shasta
	makeindex shasta
	latex shasta
	latex shasta

multlodo.tex: ../src/multlodo.tex
	cp $< $@

mountshasta.pdf: mountshasta.eps
	epstopdf mountshasta.eps

shasta.pdf:  shasta.tex intro.tex io.tex macros.tex maple.tex ref.tex\
		 title.tex multlodo.tex mountshasta.pdf
	rm -f *.aux *.ind *.idx *.toc *.ilg
	pdflatex shasta
	makeindex shasta
	pdflatex shasta
	pdflatex shasta

html.tex: shasta.tex intro.tex io.tex macros.tex maple.tex ref.tex\
		 title.tex multlodo.tex
	aldoc2html -o html.tex shasta

html.aux: html.tex
	latex html > /dev/null
	latex html > /dev/null

html/html.html: html.aux
	rm -fr html
	latex2html html
	rm -fr html.*

.PHONY: clean
clean:
	-rm *.dvi *.ps *.aux *.log *.idx *.ilg *.ind *.toc *.out *.pdf
	-rm -fr html
	-rm multlodo.tex

