#===-- lib/Core/Makefile -----------------------------------*- Makefile -*--===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#

LEVEL=../..

LIBRARYNAME=kleeCore
DONT_BUILD_RELINKED=1
BUILD_ARCHIVE=1
NO_INSTALL=1

include $(LEVEL)/Makefile.common

ifeq ($(ENABLE_BOOST),1)
  CXX.Flags := $(filter-out -fno-exceptions,$(CXX.Flags))
  C.Flags += -fsplit-stack -DBOOST_USE_SEGMENTED_STACKS
  CXX.Flags += -fsplit-stack -DBOOST_USE_SEGMENTED_STACKS
endif