//===- clang/Basic/PrettyStackTrace.h - Pretty Crash Handling --*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines the PrettyStackTraceEntry class, which is used to make
// crashes give more contextual information about what the program was doing
// when it crashed.
//
//===----------------------------------------------------------------------===//

#ifndef YASM_PRETTYSTACKTRACE_H
#define YASM_PRETTYSTACKTRACE_H

#include "llvm/Support/PrettyStackTrace.h"
#include "yasmx/Basic/SourceLocation.h"
#include "yasmx/Config/export.h"

namespace yasm {

  /// PrettyStackTraceLoc - If a crash happens while one of these objects are
  /// live, the message is printed out along with the specified source location.
  class YASM_LIB_EXPORT PrettyStackTraceLoc : public llvm::PrettyStackTraceEntry {
    SourceManager &SM;
    SourceLocation Loc;
    const char *Message;
  public:
    PrettyStackTraceLoc(SourceManager &sm, SourceLocation L, const char *Msg)
      : SM(sm), Loc(L), Message(Msg) {}
    virtual void print(llvm::raw_ostream &OS) const;
  };
}

#endif
