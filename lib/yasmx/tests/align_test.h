// Align bytecode unit test
//
//  Copyright (C) 2008  Peter Johnson
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND OTHER CONTRIBUTORS ``AS IS''
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR OTHER CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
// CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
// POSSIBILITY OF SUCH DAMAGE.
//
#include <cxxtest/TestSuite.h>

#include "yasmx/BytecodeContainer.h"
#include "yasmx/BytecodeContainer_util.h"
#include "yasmx/Bytecode.h"
#include "yasmx/Expr.h"
#include "yasmx/IntNum.h"

class AlignTestSuite : public CxxTest::TestSuite
{
public:
    void testAppendAlign()
    {
        yasm::BytecodeContainer container;
        yasm::append_align(container,
                           yasm::Expr::Ptr(new yasm::Expr(yasm::IntNum(4))),
                           yasm::Expr::Ptr(0),                  // fill
                           yasm::Expr::Ptr(0),                  // maxskip
                           0,                                   // code fill
                           5);                                  // line
        yasm::Bytecode& align = container.bcs_first();

        // align always results in contents
        TS_ASSERT(align.has_contents());
        TS_ASSERT_EQUALS(align.get_special(),
                         yasm::Bytecode::Contents::SPECIAL_OFFSET);
        TS_ASSERT_EQUALS(align.get_line(), 5UL);
        TS_ASSERT(align.get_fixed().empty());
    }
};