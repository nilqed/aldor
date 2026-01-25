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
# Targets:
#
# gmake aobj
#   makes the libsumit.al library with the .ao files
#
# gmake objects 
#   makes the libsumit.a library with the .o files
#
# gmake profile
#   makes libsumit.a.prof for profiling
#
# External variables
#
# LibDir: Name of build directory
# 	Can be changed if necessary
# SumitMLibName: Name of machine-specific library
# SUMITROOT: Root directory of the Basicmath dist.

COMPILER=axiomxl

DocDir  = $(SUMITROOT)/doc
TestDir = $(SUMITROOT)/test
LibDir  = $(SUMITROOT)/lib
IncDir  = $(SUMITROOT)/include

SUMIT=$(LibDir)/$(SumitLibName)
SUMITM=$(LibDir)/$(SumitMLibName)

# Settings for variables
include Makefile.Rules

# Various default values
SumitLibName=libsumit.al
SumitMLibName=libsumit.a


# All directories that require building
DIRS = util extree extree/operators extree/parser categories basic numbers\
	mat mat/gauss mat/modular mat/linalg\
	univpoly/categories univpoly univpoly/gcd series hompoly\
	fraction mat/linalg2 algext cond\
	polyfactorp ffield polyfactor0 skewpoly skewpoly/lodo skewpoly/lodifo\
	diffeq/series diffeq/ratsol diffeq/hypsol diffeq/liouvsol diffeq/system

TESTTARGS  = $(DIRS:%=%.test)
DOCTARGS   = $(DIRS:%=%.doc)
AOTARGS    = $(DIRS:%=%.aobj)
OBJTARGS   = $(DIRS:%=%.objects)
CLEANTARGS = $(DIRS:%=%.clean)

aobj:
	$(MAKE) aobj0 FLAGS="$(AOFLAGS)"
#	$(MAKE) aobj0 SumitLibName=$(SumitLibName).std FLAGS="$(AOFLAGS)"

aobjd:
	$(MAKE) aobj0 FLAGS="$(AODFLAGS)"
#	$(MAKE) aobj0 SumitLibName=$(SumitLibName).dbg FLAGS="$(AODFLAGS)"

doc: $(DOCTARGS)

test: $(TESTTARGS)

objects:
	$(MAKE) objects0 SumitMLibName=$(SumitMLibName).std OFLAGS="$(RELFLAGS)"

profile:
	$(MAKE) objects0 SumitMLibName=$(SumitMLibName).prof \
			 OFLAGS="$(PROFFLAGS)" 

dbg:
	$(MAKE) objects0 SumitMLibName=$(SumitMLibName).dbg \
			 OFLAGS="$(DBGFLAGS)"

clean: $(CLEANTARGS)

SUBFLAGS = FLAGS="$(FLAGS)" OFLAGS="$(OFLAGS)" \
           LibDir=$(LibDir) SUMITROOT=$(SUMITROOT) \
	   TestDir=$(TestDir) DocDir=$(DocDir) \
           SUMIT=$(SUMIT) SUMITM=$(SUMITM)

SUBMAKE = $(MAKE) $(SUBFLAGS)

# internal target
objects0: $(OBJTARGS)
	if [ -f $(LibDir)/libsumit.a ]; then $(RM) $(LibDir)/libsumit.a; fi;
	$(LN) $(SumitMLibName) $(LibDir)/libsumit.a

aobj0: $(AOTARGS)

%.include: $(IncDir)
	@(cd $*; $(SUBMAKE) include)

# %.aobj: $(LibDir)
%.aobj:
	@(cd $*; $(SUBMAKE) aobj)

%.doc: $(DocDir)
	@(cd $*; $(SUBMAKE) doc)

%.test: $(TestDir)
	@(cd $*; $(SUBMAKE) test)

%.objects: 
	@(cd $*; $(SUBMAKE) objects)

%.clean: 
	@(cd $*; $(SUBMAKE) clean)

