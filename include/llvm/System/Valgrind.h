//===- llvm/System/Valgrind.h - Communication with Valgrind -----*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Methods for communicating with a valgrind instance this program is running
// under.  These are all no-ops unless LLVM was configured on a system with the
// valgrind headers installed and valgrind is controlling this process.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_SYSTEM_VALGRIND_H
#define LLVM_SYSTEM_VALGRIND_H

#include "yasmx/Config/export.h"
#include <stddef.h>

namespace llvm {
namespace sys {
  // True if Valgrind is controlling this process.
  YASM_LIB_EXPORT
  bool RunningOnValgrind();

  // Discard valgrind's translation of code in the range [Addr .. Addr + Len).
  // Otherwise valgrind may continue to execute the old version of the code.
  YASM_LIB_EXPORT
  void ValgrindDiscardTranslations(const void *Addr, size_t Len);
}
}

#endif
