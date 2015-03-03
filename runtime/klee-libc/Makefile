#===-- runtime/klee-libc/Makefile --------------------------*- Makefile -*--===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#

LEVEL=../..

LIBRARYNAME=klee-libc
MODULE_NAME=klee-libc
#DONT_BUILD_RELINKED=1
BYTECODE_LIBRARY=1
MODULE_NAME=klee-libc
# Don't strip debug info from the module.
DEBUG_RUNTIME=1
#NO_PEDANTIC=1

# Add __NO_INLINE__ to prevent glibc from using inline definitions of some
# builtins.
C.Flags += -D__NO_INLINE__

include $(LEVEL)/Makefile.common

# LLVM < 3.4 doesn't support split stacks
ifeq ($(shell test $(LLVM_VERSION_MAJOR) -lt 3 -o $(LLVM_VERSION_MAJOR) -eq 3 -a $(LLVM_VERSION_MINOR) -lt 4; echo $$?),0)
  C.Flags := $(filter-out -fsplit-stack,$(C.Flags))
endif