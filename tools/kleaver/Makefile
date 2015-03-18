#===-- tools/kleaver/Makefile ------------------------------*- Makefile -*--===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#

LEVEL=../..
TOOLNAME = kleaver

include $(LEVEL)/Makefile.config

# FIXME: Ideally we wouldn't have any LLVM dependencies here, which
# means kicking out klee's Support.
USEDLIBS = kleeBasic.a kleaverSolver.a kleaverExpr.a kleeSupport.a 
LINK_COMPONENTS = support

include $(LEVEL)/Makefile.common

LIBS += -lstp

#ifeq ($(ENABLE_METASMT),1)
#  include $(METASMT_ROOT)/share/metaSMT/metaSMT.makefile
#  LD.Flags += -L$(METASMT_ROOT)/../../deps/Z3-4.1/lib \
#              -L$(METASMT_ROOT)/../../deps/boolector-1.5.118/lib \
#              -L$(METASMT_ROOT)/../../deps/minisat-git/lib/ \
#              -L$(METASMT_ROOT)/../../deps/boost-1_52_0/lib 
#  CXX.Flags += -DBOOST_HAS_GCC_TR1
#  CXX.Flags := $(filter-out -fno-exceptions,$(CXX.Flags)) 
#  LIBS += -lgomp -lboost_iostreams -lboost_thread -lboost_system -lmetaSMT -lz3 -lrt -lboolector -lminisat_core
#endif

ifeq ($(ENABLE_METASMT),1)
  include $(METASMT_ROOT)/share/metaSMT/metaSMT.makefile
  LD.Flags += -L$(METASMT_ROOT)/../../deps/boolector-1.5.118/lib \
              -L$(METASMT_ROOT)/../../deps/minisat-git/lib/ \
              -L$(METASMT_ROOT)/../../deps/boost-1_52_0/lib 
  CXX.Flags += -DBOOST_HAS_GCC_TR1
  CXX.Flags := $(filter-out -fno-exceptions,$(CXX.Flags)) 
  LIBS += -lgomp -lboost_iostreams -lboost_thread -lboost_system -lmetaSMT -lrt -lboolector -lminisat_core
  LIBS += -lczmq -Wl,-Bstatic -lboost_fiber -Wl,-Bdynamic -lboost_context -lcapnp -lkj
endif

ifeq ($(ENABLE_CZMQ),1)
  LD.Flags += -L$(CZMQ_ROOT)/lib
  CXX.Flags += -I$(CZMQ_ROOT)/include 
  LIBS += -lczmq
endif

ifeq ($(ENABLE_BOOST),1)
  LD.Flags += -L$(BOOST_ROOT)/lib
  CXX.Flags += -I$(BOOST_ROOT)/include
  C.Flags += -fsplit-stack -DBOOST_USE_SEGMENTED_STACKS
  CXX.Flags += -fsplit-stack -DBOOST_USE_SEGMENTED_STACKS
  LIBS += -Wl,-Bstatic -lboost_fiber -Wl,-Bdynamic -lboost_context
endif

ifeq ($(ENABLE_CAPNP),1)
  LD.Flags += -L$(CAPNP_ROOT)/lib -L$(BOOST_ROOT)/lib
  CXX.Flags += -I$(CAPNP_ROOT)/include -I$(BOOST_ROOT)/include
  LIBS += -lcapnp -lkj
  include /home/rakadjiev/workspace/metaSMT/build/root/share/metaSMT/metaSMT.makefile
  LD.Flags += -L/home/rakadjiev/workspace/metaSMT/deps/boolector-1.5.118/lib \
              -L/home/rakadjiev/workspace/metaSMT/deps/minisat-git/lib/
  CXX.Flags := $(filter-out -fno-exceptions,$(CXX.Flags)) 
  LIBS += -lgomp -lboost_iostreams -lmetaSMT -lrt -lboolector -lminisat_core
endif
