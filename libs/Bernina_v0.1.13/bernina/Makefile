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
## Download and install Aldoc 3.0 from
## ftp://ftp-sop.inria.fr/cafe/software/aldoc/aldoc.tar.gz
# export ALDOCROOT=$HOME/aldoc
# mkdir -p $ALDOCROOT
# cp aldoc.tar.gz $ALDOCROOT
# cd $ALDOCROOT
# gunzip -c aldoc.tar.gz | tar xvf -
## It seems that GCC4 cannot be used to compile Aldoc.
## So rather install, for example, gcc-3.3.
# make CC=gcc-3.3

# latex2html must be installed in order to produce html form of the
# documentation.
# Furthermore, fancyhdr.sty must be available for latex.

# You must set the following variables.

# This variable gives the path to where THIS Makefile is.
BERNINAROOT=$(shell pwd)

# This is where sumit can be found.
SUMITROOT=/path/to/sumitroot

# This variable points to the place where aldoc.cls and ttyverb.sty can
# be found. Aldoc comes with programs "extract" and "aldoc2html". If
# these programs are not in your path, then they should be under
# the following directory
ALDOCROOT=/path/to/aldoc

# If you have not yet set ALDORROOT somewhere else, you should do it here.
ALDORROOT=/path/to/aldorroot

# You don't need to change anything below this line.
ENV= \
  BERNINAROOT=$(BERNINAROOT)\
  SUMITROOT=$(SUMITROOT)\
  ALDORROOT=$(ALDORROOT)\
  ALDOCROOT=$(ALDOCROOT)\
  PATH=$(ALDOCROOT):$(ALDORROOT)/bin:$(PATH)\
  TEXINPUTS=$(ALDOCROOT):$(TEXINPUTS)

SUBMAKE=$(MAKE) $(ENV)

all: code documentation

### Compile the bernina executable.
code:
	cd $(BERNINAROOT)/src && $(SUBMAKE) all

### Check the libraries
check: testfiles
	cd $(BERNINAROOT)/test && $(SUBMAKE) $@
testfiles:
	cd $(BERNINAROOT)/src && $(SUBMAKE) test

### Everything related to producing bernina.dvi bernina.pdf and doc/html.
documentation: doc-clean dvi pdf html
texfiles:
	cd $(BERNINAROOT)/src && $(SUBMAKE) doc
dvi pdf html: texfiles
	cd $(BERNINAROOT)/doc && $(SUBMAKE) $@


### Clean the directories
clean: doc-clean
	-@$(RM) *~
	-@$(RM) */*~
	-cd $(BERNINAROOT)/src && $(SUBMAKE) clean aoclean texclean

doc-clean:
	-cd $(BERNINAROOT)/doc && $(SUBMAKE) clean

