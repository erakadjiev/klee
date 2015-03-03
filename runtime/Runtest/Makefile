#===-- runtime/Runtest/Makefile ----------------------------*- Makefile -*--===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#

LEVEL=../..

USEDLIBS=kleeBasic.a
LIBRARYNAME=kleeRuntest
SHARED_LIBRARY=1
LINK_LIBS_IN_SHARED = 1
DONT_BUILD_RELINKED = 1
NO_PEDANTIC=1

include $(LEVEL)/Makefile.common

# LLVM < 3.4 doesn't support split stacks
ifeq ($(shell test $(LLVM_VERSION_MAJOR) -lt 3 -o $(LLVM_VERSION_MAJOR) -eq 3 -a $(LLVM_VERSION_MINOR) -lt 4; echo $$?),0)
  C.Flags := $(filter-out -fsplit-stack,$(C.Flags))
endif