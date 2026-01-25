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
# make aobj
#   makes the libsumit.al library with the .ao files
#
# make objects 
#   makes the libsumit.a library with the .o files
#
#

ThisDir = diffeq_system

COMPILER=axiomxl
LibDir = $(SUMITROOT)/lib
IncDir = $(SUMITROOT)/include
DocDir = $(SUMITROOT)/doc
TestDir = $(SUMITROOT)/test
StampDir  = $(LibDir)
DocStampDir  = $(DocDir)
TestStampDir  = $(TestDir)

include ../../Makefile.Rules

AXIOMXL=${COMPILER} ${FLAGS}
AXIOMXLO=${COMPILER} ${OFLAGS}

SUMIT=$(LibDir)/libsumit.al
BSUMIT=$(LibDir)/libsumit.a

.PRECIOUS:

SRCS = sit_sys1pol sit_recsys sit_egelim

# directories that we depend on
DEPDIRS = diffeq_ratsol

NOTYET =

OBRACK = (
CBRACK = )

SRCAS   = $(SRCS:%=%.as)
AOTARGS = $(SRCS:%=$(SUMIT)$(OBRACK)%.ao$(CBRACK))
DOCTARGS = $(SRCS:%=$(DocDir)/%.tex)
TESTTARGS = $(SRCS:%=$(TestDir)/%.test.as)
OTARGS = $(SRCS:%=$(SUMITM)$(OBRACK)%.o$(CBRACK))
DEPLST  = $(DEPDIRS:%=$(StampDir)/stamp-%)
STAMP = $(StampDir)/stamp-$(ThisDir)
DOCSTAMP = $(DocStampDir)/stamp-$(ThisDir)
TESTSTAMP = $(TestStampDir)/stamp-$(ThisDir)

OKFILES = Makefile $(SRCAS) $(NOTYET)

test: $(TESTSTAMP)

doc: $(DOCSTAMP)

aobj: $(STAMP)

objects: $(SUMITM)

clean:
	-@rm -f *.c *.h *.fm *.ao *.o *~

$(TESTSTAMP): $(TESTTARGS)
	touch $(TESTSTAMP)

$(DOCSTAMP): $(DOCTARGS)
	touch $(DOCSTAMP)

$(STAMP): $(AOTARGS)
	touch $(STAMP)

$(SUMITM): $(STAMP) $(OTARGS)
	ranlib $(SUMITM) || true

# Explicit dependencies
OD = $(DEPLST)

${SUMIT}(sit_egelim.ao):	${SUMIT}(sit_linalg.ao)
${SUMIT}(sit_sys1pol.ao): ${SUMIT}(sit_lin2rec.ao) ${SUMIT}(sit_sys1tls.ao) ${SUMIT}(sit_egelim.ao)
${SUMIT}(sit_recsys.ao): ${SUMIT}(sit_system1.ao) ${SUMIT}(sit_sys1pol.ao)
