//
// NASM-compatible parser
//
//  Copyright (C) 2001-2007  Peter Johnson, Michael Urman
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
#define DEBUG_TYPE "NasmParser"

#include <util.h>

#include <math.h>

#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/Statistic.h"
#include "yasmx/Parse/IdentifierTable.h"
#include "yasmx/Support/bitcount.h"
#include "yasmx/Arch.h"
#include "yasmx/Bytecode.h"
#include "yasmx/BytecodeContainer.h"
#include "yasmx/Bytes.h"
#include "yasmx/Bytes_util.h"
#include "yasmx/Diagnostic.h"
#include "yasmx/Directive.h"
#include "yasmx/EffAddr.h"
#include "yasmx/Errwarns.h"
#include "yasmx/Expr.h"
#include "yasmx/NameValue.h"
#include "yasmx/Object.h"
#include "yasmx/Section.h"
#include "yasmx/Symbol.h"

#include "modules/parsers/nasm/NasmParser.h"
#include "modules/parsers/nasm/NasmLexer.h"
#include "modules/parsers/nasm/NasmNumericParser.h"
#include "modules/parsers/nasm/NasmStringParser.h"


STATISTIC(num_pseudo_insn_lookup, "Number of pseudo-instruction lookups");
STATISTIC(num_keyword_lookup, "Number of keyword lookups");
STATISTIC(num_directive, "Number of directives parsed");
STATISTIC(num_insn, "Number of instructions parsed");
STATISTIC(num_insn_operand, "Number of instruction operands parsed");

using namespace yasm;
using namespace yasm::parser;

/// Identify pseudo-instructions.  We can't simply pre-populate IdentifierTable
/// because of large numbers of combinations due to case-insensitivity.
void
NasmParser::CheckPseudoInsn(IdentifierInfo* ii)
{
    /// All possible pseudo-instructions (to avoid dynamic allocation).
    static const PseudoInsn equ_insn = {PseudoInsn::EQU, 0};
    static const PseudoInsn incbin_insn = {PseudoInsn::INCBIN, 0};

    if (!ii->isUnknown())
        return;

    ++num_pseudo_insn_lookup;
    PseudoInsn* pseudo;

    // Do a case-insensitive match against pseudoinstructions.
    // This is a fairly "hot" piece of code.
    const char* name = ii->getNameStart();
    unsigned int len = ii->getLength();
    switch (name[0])
    {
        case 'e':
        case 'E':
            // EQU
            if (len != 3 ||
                (name[1] != 'q' && name[1] != 'Q') ||
                (name[2] != 'u' && name[2] != 'U'))
                return;
            ii->setCustom(&equ_insn);
            return;
        case 'i':
        case 'I':
            // INCBIN
            if (len != 6 ||
                (name[1] != 'n' && name[1] != 'N') ||
                (name[2] != 'c' && name[2] != 'C') ||
                (name[3] != 'b' && name[3] != 'B') ||
                (name[4] != 'i' && name[4] != 'I') ||
                (name[5] != 'n' && name[5] != 'N'))
                return;
            ii->setCustom(&incbin_insn);
            return;
        case 'd':
        case 'D':
            // Declare data
            if (len > 3)
                return;
            pseudo = m_data_insns;
            ++name;
            break;
        case 'r':
        case 'R':
            // Reserve space
            if (len > 5 ||
                (name[1] != 'e' && name[1] != 'E') ||
                (name[2] != 's' && name[2] != 'S'))
                return;
            pseudo = m_reserve_insns;
            name += 3;
            break;
        default:
            return;
    }

    // Handle declare data / reserve space size lookup
    unsigned int idx = 0;
    switch (name[0])
    {
        case 'b':   idx = DB; ++name; break;
        case 'h':
            if (name[1] != 'w')
                return;
            idx = DHW;
            name += 2;
            break;
        case 'w':   idx = DW; ++name; break;
        case 'd':
            idx = DD;
            ++name;
            if (name[0] == 'q')
            {
                idx = DO;       // ddq is an alias for do
                ++name;
            }
            break;
        case 'q':   idx = DQ; ++name; break;
        case 't':   idx = DT; ++name; break;
        case 'o':   idx = DO; ++name; break;
        case 'y':   idx = DY; ++name; break;
        default:    return;
    }

    if (name[0] != '\0')
        return;
    ii->setCustom(&pseudo[idx]);
}

/// Identify keywords.  We can't simply pre-populate IdentifierTable
/// because of large numbers of combinations due to case-insensitivity.
bool
NasmParser::CheckKeyword(IdentifierInfo* ii)
{
    if (!ii->isUnknown())
        return false;

    ++num_keyword_lookup;

    // Do a case-insensitive match against keywords.
    // This is a fairly "hot" piece of code.
    const char* name = ii->getNameStart();
    unsigned int len = ii->getLength();
    int kind = NasmToken::unknown;

    switch (name[0])
    {
        case 'a':
        case 'A':
            // ABS
            if (len != 3 ||
                (name[1] != 'b' && name[1] != 'B') ||
                (name[2] != 's' && name[2] != 'S'))
                return false;
            ii->setTokenKind(NasmToken::kw_abs);
            m_token.setKind(NasmToken::kw_abs);
            return true;
        case 'b':
        case 'B':
            // BYTE
            if (len != 4 ||
                (name[1] != 'y' && name[1] != 'Y') ||
                (name[2] != 't' && name[2] != 'T') ||
                (name[3] != 'e' && name[3] != 'E'))
                return false;
            ii->setTokenKind(NasmToken::kw_byte);
            m_token.setKind(NasmToken::kw_byte);
            return true;
        case 'd':
        case 'D':
            // DWORD
            if (len == 5)
            {
                kind = NasmToken::kw_dword;
                ++name;
                break;  // check for "WORD" suffix
            }
            // DQWORD
            if (len == 6 &&
                (name[1] == 'q' || name[1] == 'Q'))
            {
                kind = NasmToken::kw_dqword;
                name += 2;
                break;  // check for "WORD" suffix
            }
            return false;
        case 'h':
        case 'H':
            // HWORD
            if (len != 5)
                return false;
            kind = NasmToken::kw_hword;
            ++name;
            break;  // check for "WORD" suffix
        case 'l':
        case 'L':
            // LONG
            if (len != 4 ||
                (name[1] != 'o' && name[1] != 'O') ||
                (name[2] != 'n' && name[2] != 'N') ||
                (name[3] != 'g' && name[3] != 'G'))
                return false;
            ii->setTokenKind(NasmToken::kw_long);
            m_token.setKind(NasmToken::kw_long);
            return true;
        case 'n':
        case 'N':
            // NOSPLIT
            if (len != 7 ||
                (name[1] != 'o' && name[1] != 'O') ||
                (name[2] != 's' && name[2] != 'S') ||
                (name[3] != 'p' && name[3] != 'P') ||
                (name[4] != 'l' && name[4] != 'L') ||
                (name[5] != 'i' && name[5] != 'I') ||
                (name[6] != 't' && name[6] != 'T'))
                return false;
            ii->setTokenKind(NasmToken::kw_nosplit);
            m_token.setKind(NasmToken::kw_nosplit);
            return true;
        case 'o':
        case 'O':
            // OWORD
            if (len != 5)
                return false;
            kind = NasmToken::kw_oword;
            ++name;
            break;  // check for "WORD" suffix
        case 'q':
        case 'Q':
            // QWORD
            if (len != 5)
                return false;
            kind = NasmToken::kw_qword;
            ++name;
            break;  // check for "WORD" suffix
        case 'r':
        case 'R':
            // REL
            if (len != 3 ||
                (name[1] != 'e' && name[1] != 'E') ||
                (name[2] != 'l' && name[2] != 'L'))
                return false;
            ii->setTokenKind(NasmToken::kw_rel);
            m_token.setKind(NasmToken::kw_rel);
            return true;
        case 's':
        case 'S':
            // SEG
            if (len == 3 &&
                (name[1] == 'e' || name[1] == 'E') &&
                (name[2] == 'g' || name[2] == 'G'))
            {
                ii->setTokenKind(NasmToken::kw_seg);
                m_token.setKind(NasmToken::kw_seg);
                return true;
            }
            if (len == 6 &&
                (name[1] == 't' || name[1] == 'T') &&
                (name[2] == 'r' || name[2] == 'R') &&
                (name[3] == 'i' || name[3] == 'I') &&
                (name[4] == 'c' || name[4] == 'C') &&
                (name[5] == 't' || name[5] == 'T'))
            {
                ii->setTokenKind(NasmToken::kw_strict);
                m_token.setKind(NasmToken::kw_strict);
                return true;
            }
        case 't':
        case 'T':
            // TIMES or TWORD
            if (len != 5)
                return false;
            // TWORD
            if ((name[1] == 'w' || name[1] == 'W'))
            {
                kind = NasmToken::kw_tword;
                ++name;
                break;  // check for "WORD" suffix
            }
            // TIMES
            if ((name[1] != 'i' && name[1] != 'I') ||
                (name[2] != 'm' && name[2] != 'M') ||
                (name[3] != 'e' && name[3] != 'E') ||
                (name[4] != 's' && name[4] != 'S'))
                return false;
            ii->setTokenKind(NasmToken::kw_times);
            m_token.setKind(NasmToken::kw_times);
            return true;
        case 'w':
        case 'W':
            // WRT
            if (len == 3 &&
                (name[1] == 'r' || name[1] == 'R') &&
                (name[2] == 't' || name[2] == 'T'))
            {
                ii->setTokenKind(NasmToken::kw_wrt);
                m_token.setKind(NasmToken::kw_wrt);
                return true;
            }
            // WORD
            if (len != 4)
                return false;
            kind = NasmToken::kw_word;
            break;  // check for "WORD" suffix
        case 'y':
        case 'Y':
            // YWORD
            if (len != 5)
                return false;
            kind = NasmToken::kw_yword;
            ++name;
            break;  // check for "WORD" suffix
        default:
            return false;
    }

    // Common "WORD" suffix matching
    if ((name[0] != 'w' && name[0] != 'W') ||
        (name[1] != 'o' && name[1] != 'O') ||
        (name[2] != 'r' && name[2] != 'R') ||
        (name[3] != 'd' && name[3] != 'D'))
        return false;
    ii->setTokenKind(kind);
    m_token.setKind(kind);
    return true;
}

void
NasmParser::DoParse()
{
    Bytecode::Ptr bc(new Bytecode());

    while (m_token.isNot(NasmToken::eof))
    {
        if (!m_abspos.isEmpty())
            m_bc = bc.get();
        else
            m_bc = &m_object->getCurSection()->FreshBytecode();

        if (m_token.isEndOfStatement())
            ConsumeToken();
        else
        {
            ParseLine();
            SkipUntil(NasmToken::eol);
        }
#if 0
            if (m_abspos.get() != 0)
            {
                // If we're inside an absolute section, just add to the
                // absolute position rather than appending bytecodes to a
                // section.  Only RES* are allowed in an absolute section,
                // so this is easy.
                if (m_bc->has_contents())
                {
                    unsigned int itemsize;
                    const Expr* numitems = m_bc->reserve_numitems(itemsize);
                    if (numitems)
                    {
                        Expr::Ptr e(new Expr(numitems->clone(),
                                             Op::MUL,
                                             new IntNum(itemsize),
                                             cur_line));
                        const Expr* multiple = m_bc->getMultipleExpr();
                        if (multiple)
                            e.reset(new Expr(e.release(),
                                             Op::MUL,
                                             multiple->clone(),
                                             cur_line));
                        m_abspos.reset(new Expr(m_abspos.release(),
                                                Op::ADD,
                                                e,
                                                cur_line));
                    }
                    else
                        throw SyntaxError(
                            N_("only RES* allowed within absolute section"));
                    bc.reset(new Bytecode());
                }
            }
#endif
    }
}

// All Parse* functions expect to be called with m_token being their first
// token.  They should return with m_token being the token *after* their
// information.

bool
NasmParser::ParseLine()
{
    m_container = m_object->getCurSection();

    if (ParseExp())
        return true;

    switch (m_token.getKind())
    {
#if 0
        case LINE: // LINE INTNUM '+' INTNUM FILENAME
        {
            getNextToken();

            if (!Expect(INTNUM, diag::err_expected_integer))
                return false;
            std::auto_ptr<IntNum> line(INTNUM_val);
            getNextToken();

            if (!ExpectAndConsume('+', diag::err_expected_plus))
                return false;

            if (!Expect(INTNUM, diag::err_expected_integer))
                return false;
            std::auto_ptr<IntNum> incr(INTNUM_val);
            getNextToken();

            if (!Expect(FILENAME, diag::err_expected_filename))
                return false;
            std::string filename;
            std::swap(filename, FILENAME_val);
            getNextToken();

            // %line indicates the line number of the *next* line, so subtract
            // out the increment when setting the line number.
            // FIXME: handle incr
            clang::SourceManager& smgr = m_preproc->getSourceManager();
            smgr.AddLineNote(m_source, line->getUInt(),
                             smgr.getLineTableFilenameID(filename.data(),
                                                         filename.size()));
            break;
        }
#endif
        case NasmToken::l_square: // [ directive ]
        {
            clang::SourceLocation lsquare_loc = ConsumeBracket();

            if (m_token.isNot(NasmToken::identifier))
            {
                Diag(m_token, diag::err_expected_directive_name);
                return false;
            }
            llvm::SmallString<64> dirname_buf;
            llvm::StringRef dirname =
                m_preproc.getSpelling(m_token, dirname_buf);
            clang::SourceLocation dirloc = ConsumeToken();

            // catch [directive<eol> early (XXX: better way to do this?)
            if (m_token.isEndOfStatement())
            {
                MatchRHSPunctuation(NasmToken::r_square, lsquare_loc);
                return false;
            }

            DirectiveInfo info(*m_object, dirloc);
            // Parse "normal" directive namevals, if present
            if (m_token.isNot(NasmToken::r_square) &&
                m_token.isNot(NasmToken::colon))
            {
                if (!ParseDirective(info.getNameValues()))
                    return false;
            }

            // Parse "extended" directive namevals, if present
            if (m_token.is(NasmToken::colon))
            {
                ConsumeToken();
                if (!ParseDirective(info.getObjextNameValues()))
                    return false;
            }

            // Directive should end with a ]
            MatchRHSPunctuation(NasmToken::r_square, lsquare_loc);

            // Pass directive namevals to appropriate handler
            DoDirective(dirname, info);
            break;
        }
        case NasmToken::kw_times: // TIMES expr exp
            return ParseTimes(ConsumeToken());
        case NasmToken::identifier:
        case NasmToken::label:
        {
            // Might be any one of the following cases:
            // LABEL
            // LABEL:
            // LABEL EQU val
            // LABEL: EQU val
            // (INSN args is caught by ParseExp() call above)
            IdentifierInfo* ii = m_token.getIdentifierInfo();
            clang::SourceLocation id_source = ConsumeToken();

            // Eat the (optional) colon if it is present
            bool got_colon = false;
            if (m_token.is(NasmToken::colon))
            {
                got_colon = true;
                ConsumeToken();
            }

            // Check for EQU case
            if (m_token.is(Token::identifier))
            {
                IdentifierInfo* ii2 = m_token.getIdentifierInfo();
                CheckPseudoInsn(ii2);
                const PseudoInsn* pseudo = ii2->getCustom<const PseudoInsn>();
                if (pseudo && pseudo->type == PseudoInsn::EQU)
                {
                    // label EQU expr
                    ConsumeToken();
                    Expr e;
                    if (!ParseExpr(e, NORM_EXPR))
                    {
                        Diag(m_token, diag::err_expected_expression_after)
                            << ii2->getName();
                        return false;
                    }
                    ParseSymbol(ii)->CheckedDefineEqu(e, id_source,
                        m_preproc.getDiagnostics());
                    break;
                }
            }

            // Otherwise must be a label
            bool local;
            SymbolRef sym = ParseSymbol(ii, &local);
            DefineLabel(sym, id_source, local);
            if (m_token.isEndOfStatement())
            {
                // Label alone on the line.
                if (!got_colon)
                    Diag(m_token, diag::warn_orphan_label);
                break;
            }
            if (m_token.is(NasmToken::kw_times))
            {
                return ParseTimes(ConsumeToken());
            }
            if (!ParseExp())
            {
                Diag(m_token, diag::err_expected_insn_after_label);
                return false;
            }
            break;
        }
        default:
            Diag(m_token, diag::err_expected_insn_or_label_after_eol);
            return false;
    }
    return true;
}

bool
NasmParser::ParseDirective(/*@out@*/ NameValues& nvs)
{
    for (;;)
    {
        std::string name;
        std::auto_ptr<NameValue> nv(0);
        clang::SourceLocation name_loc, equals_loc;

        // Look for value first
        if (m_token.is(NasmToken::identifier) || m_token.is(NasmToken::label))
        {
            if (NextToken().is(NasmToken::equal))
            {
                name = m_preproc.getSpelling(m_token);
                name_loc = ConsumeToken(); // id
                equals_loc = ConsumeToken(); // '='
            }
        }

        // Look for parameter
        switch (m_token.getKind())
        {
            case NasmToken::string_literal:
            {
                NasmStringParser str(m_token.getLiteral(),
                                     m_token.getLocation(), m_preproc);
                if (str.hadError())
                    nv.reset(new NameValue(name, ""));
                else
                {
                    llvm::SmallString<64> strbuf;
                    nv.reset(new NameValue(name, str.getString(strbuf)));
                }
                /// XXX: full range of string token?
                nv->setValueRange(ConsumeToken());
                break;
            }
            case NasmToken::identifier:
            case NasmToken::label:
                // We cheat and peek ahead to see if this is just an ID or
                // the ID is part of an expression.  We assume a + or - means
                // that it's part of an expression (e.g. "x+y" is parsed as
                // the expression "x+y" and not as "x", "+y").
                switch (NextToken().getKind())
                {
                    case NasmToken::amp:
                    case NasmToken::star:
                    case NasmToken::plus:
                    case NasmToken::minus:
                    case NasmToken::tilde:
                    case NasmToken::slash:
                    case NasmToken::slashslash:
                    case NasmToken::percent:
                    case NasmToken::percentpercent:
                    case NasmToken::lessless:
                    case NasmToken::greatergreater:
                    case NasmToken::caret:
                    case NasmToken::pipe:
                        break;
                    default:
                        // Just an id
                        nv.reset(new NameValue(name,
                                               m_preproc.getSpelling(m_token),
                                               '$'));
                        /// XXX: full range of ID?
                        nv->setValueRange(ConsumeToken());
                        goto next;
                }
                /*@fallthrough@*/
            default:
            {
                Expr::Ptr e(new Expr);
                if (!ParseExpr(*e, DIR_EXPR))
                {
                    Diag(m_token, diag::err_invalid_directive_argument);
                    return false;
                }
                nv.reset(new NameValue(name, e));
                break;
            }
        }
next:
        nv->setNameSource(name_loc);
        nv->setEqualsSource(equals_loc);
        nvs.push_back(nv.release());

        // silently eat commas
        if (m_token.is(NasmToken::comma))
            ConsumeToken();
        if (m_token.is(NasmToken::r_square) ||
            m_token.is(NasmToken::colon) ||
            m_token.isEndOfStatement())
            return true;
    }
}

bool
NasmParser::ParseTimes(clang::SourceLocation times_source)
{
    Expr::Ptr multiple(new Expr);
    if (!ParseBExpr(*multiple, DV_EXPR))
    {
        Diag(m_token, diag::err_expected_expression_after_id)
            << "TIMES";
        return false;
    }
    BytecodeContainer* orig_container = m_container;
    m_container = &AppendMultiple(*m_container, multiple, times_source);

    clang::SourceLocation cursource = m_token.getLocation();
    if (!ParseExp())
    {
        Diag(cursource, diag::err_expected_insn_after_times);
        m_container = orig_container;
        return false;
    }
    m_container = orig_container;
    return true;
}

bool
NasmParser::ParseExp()
{
    clang::SourceLocation exp_source = m_token.getLocation();
    Insn::Ptr insn = ParseInsn();
    if (insn.get() != 0)
    {
        insn->Append(*m_container, exp_source, m_preproc.getDiagnostics());
        return true;
    }

    if (m_token.isNot(NasmToken::identifier))
        return false;

    IdentifierInfo* ii = m_token.getIdentifierInfo();
    CheckPseudoInsn(ii);
    const PseudoInsn* pseudo = ii->getCustom<const PseudoInsn>();
    if (!pseudo)
        return false;

    switch (pseudo->type)
    {
        case PseudoInsn::DECLARE_DATA:
        {
            ConsumeToken();

            for (;;)
            {
                if (m_token.is(NasmToken::string_literal))
                {
                    // Peek ahead to see if we're in an expr.  If we're not,
                    // then generate a real string dataval.
                    const Token& peek_token = NextToken();
                    if (peek_token.is(NasmToken::comma) ||
                        peek_token.isEndOfStatement())
                    {
                        NasmStringParser str(m_token.getLiteral(),
                                             m_token.getLocation(), m_preproc);
                        if (!str.hadError())
                        {
                            llvm::SmallString<64> strbuf;
                            AppendData(*m_container, str.getString(strbuf),
                                       pseudo->size, false);
                        }
                        ConsumeToken();
                        goto dv_done;
                    }
                }
                {
                    Expr::Ptr e(new Expr);
                    if (ParseBExpr(*e, DV_EXPR))
                        AppendData(*m_container, e, pseudo->size, *m_arch,
                                   exp_source);
                    else
                    {
                        Diag(m_token, diag::err_expected_expression_or_string);
                        break;
                    }
                }
dv_done:
                if (m_token.isEndOfStatement())
                    break;
                ExpectAndConsume(NasmToken::comma, diag::err_expected_comma);
                if (m_token.isEndOfStatement())
                    break;  // allow trailing , on list
            }
            return true;
        }
        case PseudoInsn::RESERVE_SPACE:
        {
            ConsumeToken();
            Expr::Ptr e(new Expr);
            if (!ParseBExpr(*e, DV_EXPR))
            {
                Diag(m_token, diag::err_expected_expression_after_id)
                    << "RESx";
                return false;
            }
            BytecodeContainer& multc =
                AppendMultiple(*m_container, e, exp_source);
            multc.AppendGap(pseudo->size, exp_source);
            return true;
        }
        case PseudoInsn::INCBIN:
        {
            ConsumeToken();

            if (m_token.isNot(NasmToken::string_literal))
            {
                Diag(m_token, diag::err_incbin_expected_filename);
                return false;
            }

            NasmStringParser str(m_token.getLiteral(), m_token.getLocation(),
                                 m_preproc);
            llvm::SmallString<64> strbuf;
            llvm::StringRef filename;
            if (!str.hadError())
                filename = str.getString(strbuf);
            ConsumeToken();

            Expr::Ptr start(0), maxlen(0);

            // optional start expression
            if (m_token.is(NasmToken::comma))
                ConsumeToken();
            if (m_token.isEndOfStatement())
                goto incbin_done;
            start.reset(new Expr);
            if (!ParseBExpr(*start, DV_EXPR))
            {
                Diag(m_token, diag::err_incbin_expected_start_expression);
                return false;
            }

            // optional maxlen expression
            if (m_token.is(NasmToken::comma))
                ConsumeToken();
            if (m_token.isEndOfStatement())
                goto incbin_done;
            maxlen.reset(new Expr);
            if (!ParseBExpr(*maxlen, DV_EXPR))
            {
                Diag(m_token, diag::err_incbin_expected_length_expression);
                return false;
            }

incbin_done:
            AppendIncbin(*m_container, filename, start, maxlen, exp_source);
            return true;
        }
        default:
            break;
    }
    return false;
}

Insn::Ptr
NasmParser::ParseInsn()
{
    if (m_token.isNot(NasmToken::identifier))
        return Insn::Ptr(0);

    IdentifierInfo* ii = m_token.getIdentifierInfo();
    ii->DoInsnLookup(*m_arch, m_token.getLocation(),
                     m_preproc.getDiagnostics());
    if (const Arch::InsnInfo* insninfo = ii->getInsn())
    {
        ConsumeToken();
        ++num_insn;
        Insn::Ptr insn(m_arch->CreateInsn(insninfo));
        if (m_token.isEndOfStatement())
            return insn;    // no operands

        // parse operands
        for (;;)
        {
            clang::SourceLocation start = m_token.getLocation();
            ++num_insn_operand;
            Operand op = ParseOperand();
            op.setSource(start);
            insn->AddOperand(op);

            if (m_token.isEndOfStatement())
                break;
            if (ExpectAndConsume(NasmToken::comma, diag::err_expected_comma))
                break;
        }
        return insn;
    }
    if (const Prefix* prefix = ii->getPrefix())
    {
        clang::SourceLocation prefix_source = ConsumeToken();
        Insn::Ptr insn = ParseInsn();
        if (insn.get() == 0)
            insn = m_arch->CreateEmptyInsn();
        insn->AddPrefix(prefix, prefix_source);
        return insn;
    }
    ii->DoRegLookup(*m_arch, m_token.getLocation(), m_preproc.getDiagnostics());
    if (const SegmentRegister* segreg = ii->getSegReg())
    {
        clang::SourceLocation segreg_source = ConsumeToken();
        Insn::Ptr insn = ParseInsn();
        if (insn.get() == 0)
            insn = m_arch->CreateEmptyInsn();
        else if (insn->hasSegPrefix())
            Diag(segreg_source, diag::warn_multiple_seg_override);
        insn->setSegPrefix(segreg, segreg_source);
        return insn;
    }

    return Insn::Ptr(0);
}

// Map token to size override value.  If not recognized, returns 0.
unsigned int
NasmParser::getSizeOverride(Token& tok)
{
    switch (tok.getKind())
    {
        case NasmToken::kw_byte:    return 8;
        case NasmToken::kw_hword:   return m_wordsize/2;
        case NasmToken::kw_word:    return m_wordsize;
        case NasmToken::kw_dword:
        case NasmToken::kw_long:    return m_wordsize*2;
        case NasmToken::kw_qword:   return m_wordsize*4;
        case NasmToken::kw_oword:
        case NasmToken::kw_dqword:  return m_wordsize*8;
        case NasmToken::kw_tword:   return 80;
        case NasmToken::kw_yword:   return 256;
        default:                    return 0;
    }
}

Operand
NasmParser::ParseOperand()
{
    // Look for size override keywords
    unsigned int size = getSizeOverride(m_token);
    if (size != 0)
    {
        clang::SourceLocation override_loc = ConsumeToken();
        Operand op = ParseOperand();
        const Register* reg = op.getReg();
        if (reg && reg->getSize() != size)
            Diag(override_loc, diag::err_register_size_override);
        else
        {
            // Silently override others unless a warning is turned on.
            // This is to allow overrides such as:
            //   %define arg1 dword [bp+4]
            //   cmp word arg1, 2
            // Which expands to:
            //   cmp word dword [bp+4], 2
            unsigned int opsize = op.getSize();
            if (opsize != 0)
            {
                if (opsize != size)
                    Diag(override_loc, diag::warn_operand_size_override)
                        << opsize << size;
                else
                    Diag(override_loc, diag::warn_operand_size_duplicate);
            }
            op.setSize(size);
        }
        return op;
    }

    switch (m_token.getKind())
    {
        case NasmToken::l_square:
        {
            clang::SourceLocation lsquare_loc = ConsumeBracket();
            Operand op = ParseMemoryAddress();
            MatchRHSPunctuation(NasmToken::r_square, lsquare_loc);
            return op;
        }
        case NasmToken::kw_strict:
        {
            ConsumeToken();
            Operand op = ParseOperand();
            op.setStrict();
            return op;
        }
        case NasmToken::identifier:
        {
            // Look for register, etc. matches
            IdentifierInfo* ii = m_token.getIdentifierInfo();
            ii->DoRegLookup(*m_arch, m_token.getLocation(),
                            m_preproc.getDiagnostics());
            if (const Register* reg = ii->getRegister())
            {
                Operand op(reg);
                ConsumeToken();
                return op;
            }
            if (const SegmentRegister* segreg = ii->getSegReg())
            {
                Operand op(segreg);
                ConsumeToken();
                return op;
            }
            if (const TargetModifier* tmod = ii->getTargetModifier())
            {
                ConsumeToken();
                Operand op = ParseOperand();
                op.setTargetMod(tmod);
                return op;
            }
            // Might be an unrecognized keyword.
            if (CheckKeyword(ii))
                return ParseOperand();  // recognized, reparse
            /*@fallthrough@*/
        }
        default:
        {
            Expr::Ptr e(new Expr);
            if (!ParseBExpr(*e, NORM_EXPR))
            {
                Diag(m_token, diag::err_expected_operand);
                return Operand(e);
            }
            if (m_token.isNot(NasmToken::colon))
                return Operand(e);
            ConsumeToken();
            Expr::Ptr off(new Expr);
            if (!ParseBExpr(*off, NORM_EXPR))
            {
                Diag(m_token, diag::err_expected_expression_after)
                    << ":";
                return Operand(e);
            }
            Operand op(off);
            op.setSeg(e);
            return op;
        }
    }
}

// memory addresses
Operand
NasmParser::ParseMemoryAddress()
{
    // Look for size override keywords
    unsigned int size = getSizeOverride(m_token);
    if (size != 0)
    {
        ConsumeToken();
        Operand op = ParseMemoryAddress();
        op.getMemory()->m_disp.setSize(size);
        return op;
    }

    switch (m_token.getKind())
    {
        case NasmToken::kw_nosplit:
        {
            ConsumeToken();
            Operand op = ParseMemoryAddress();
            op.getMemory()->m_nosplit = true;
            return op;
        }
        case NasmToken::kw_rel:
        {
            ConsumeToken();
            Operand op = ParseMemoryAddress();
            EffAddr* ea = op.getMemory();
            ea->m_pc_rel = true;
            ea->m_not_pc_rel = false;
            return op;
        }
        case NasmToken::kw_abs:
        {
            ConsumeToken();
            Operand op = ParseMemoryAddress();
            EffAddr* ea = op.getMemory();
            ea->m_pc_rel = false;
            ea->m_not_pc_rel = true;
            return op;
        }
        case NasmToken::identifier:
        {
            IdentifierInfo* ii = m_token.getIdentifierInfo();
            // See if it's a segment register first.
            ii->DoRegLookup(*m_arch, m_token.getLocation(),
                            m_preproc.getDiagnostics());
            if (const SegmentRegister* segreg = ii->getSegReg())
            {
                clang::SourceLocation segreg_source = ConsumeToken();

                ExpectAndConsume(NasmToken::colon,
                                 diag::err_colon_required_after_segreg);

                Operand op = ParseMemoryAddress();
                if (EffAddr* ea = op.getMemory())
                {
                    if (ea->m_segreg != 0)
                        Diag(segreg_source, diag::warn_multiple_seg_override);
                    ea->m_segreg = segreg;
                }
                return op;
            }
            // Might be an unrecognized keyword.
            if (CheckKeyword(ii))
                return ParseMemoryAddress();    // recognized, reparse
            /*@fallthrough@*/
        }
        default:
        {
            Expr::Ptr e(new Expr);
            if (!ParseBExpr(*e, NORM_EXPR))
            {
                Diag(m_token, diag::err_expected_memory_address);
                return Operand(e);
            }
            if (m_token.isNot(NasmToken::colon))
                return Operand(m_object->getArch()->CreateEffAddr(e));
            ConsumeToken();
            Expr::Ptr off(new Expr);
            if (!ParseBExpr(*off, NORM_EXPR))
            {
                Diag(m_token, diag::err_expected_expression_after)
                    << ":";
                return Operand(e);
            }
            Operand op(m_object->getArch()->CreateEffAddr(off));
            op.setSeg(e);
            return op;
        }
    }
}

// Expression grammar parsed is:
//
// expr  : bexpr [ : bexpr ]
// bexpr : expr0 [ WRT expr6 ]
// expr0 : expr1 [ {|} expr1...]
// expr1 : expr2 [ {^} expr2...]
// expr2 : expr3 [ {&} expr3...]
// expr3 : expr4 [ {<<,>>} expr4...]
// expr4 : expr5 [ {+,-} expr5...]
// expr5 : expr6 [ {*,/,%,//,%%} expr6...]
// expr6 : { ~,+,-,SEG } expr6
//       | (expr)
//       | symbol
//       | $
//       | number

#define ParseExprCommon(leftfunc, tok, rightfunc, op) \
    do {                                              \
        if (!leftfunc(e, type))                       \
            return false;                             \
                                                      \
        while (m_token.is(tok))                       \
        {                                             \
            ConsumeToken();                           \
            Expr f;                                   \
            if (!rightfunc(f, type))                  \
                return false;                         \
            e.Calc(op, f);                            \
        }                                             \
        return true;                                  \
    } while(0)

bool
NasmParser::ParseExpr(Expr& e, ExprType type)
{
    switch (type)
    {
        case DIR_EXPR:
            // directive expressions can't handle seg:off or WRT
            return ParseExpr0(e, type);
        default:
            ParseExprCommon(ParseBExpr, NasmToken::colon, ParseBExpr,
                            Op::SEGOFF);
    }
    /*@notreached@*/
    return false;
}

bool
NasmParser::ParseBExpr(Expr& e, ExprType type)
{
    if (!ParseExpr0(e, type))
        return false;

    for (;;)
    {
        if (m_token.is(NasmToken::identifier))
        {
            IdentifierInfo* ii = m_token.getIdentifierInfo();
            if (!CheckKeyword(ii))
                break;
        }
        if (m_token.isNot(NasmToken::kw_wrt))
            break;
        ConsumeToken();
        Expr f;
        if (!ParseExpr6(f, type))
            return false;
        e.Calc(Op::WRT, f);
    }
    return true;
}

bool
NasmParser::ParseExpr0(Expr& e, ExprType type)
{
    ParseExprCommon(ParseExpr1, NasmToken::pipe, ParseExpr1, Op::OR);
}

bool
NasmParser::ParseExpr1(Expr& e, ExprType type)
{
    ParseExprCommon(ParseExpr2, NasmToken::caret, ParseExpr2, Op::XOR);
}

bool
NasmParser::ParseExpr2(Expr& e, ExprType type)
{
    ParseExprCommon(ParseExpr3, NasmToken::amp, ParseExpr3, Op::AND);
}

bool
NasmParser::ParseExpr3(Expr& e, ExprType type)
{
    if (!ParseExpr4(e, type))
        return false;

    for (;;)
    {
        Op::Op op;
        switch (m_token.getKind())
        {
            case NasmToken::lessless:       op = Op::SHL; break;
            case NasmToken::greatergreater: op = Op::SHR; break;
            default: return true;
        }
        ConsumeToken();

        Expr f;
        if (!ParseExpr4(f, type))
            return false;
        e.Calc(op, f);
    }
}

bool
NasmParser::ParseExpr4(Expr& e, ExprType type)
{
    if (!ParseExpr5(e, type))
        return false;

    for (;;)
    {
        Op::Op op;
        switch (m_token.getKind())
        {
            case NasmToken::plus:   op = Op::ADD; break;
            case NasmToken::minus:  op = Op::SUB; break;
            default: return true;
        }
        ConsumeToken();

        Expr f;
        if (!ParseExpr5(f, type))
            return false;
        e.Calc(op, f);
    }
}

bool
NasmParser::ParseExpr5(Expr& e, ExprType type)
{
    if (!ParseExpr6(e, type))
        return false;

    for (;;)
    {
        Op::Op op;
        switch (m_token.getKind())
        {
            case NasmToken::star:           op = Op::MUL; break;
            case NasmToken::slash:          op = Op::DIV; break;
            case NasmToken::percent:        op = Op::MOD; break;
            case NasmToken::slashslash:     op = Op::SIGNDIV; break;
            case NasmToken::percentpercent: op = Op::SIGNMOD; break;
            default: return true;
        }
        ConsumeToken();

        Expr f;
        if (!ParseExpr6(f, type))
            return false;
        e.Calc(op, f);
    }
}

bool
NasmParser::ParseExpr6(Expr& e, ExprType type)
{
    // directives allow very little and handle IDs specially
    if (type == DIR_EXPR)
    {
        switch (m_token.getKind())
        {
        case NasmToken::tilde:
            ConsumeToken();
            if (!ParseExpr6(e, type))
                return false;
            e.Calc(Op::NOT);
            return true;
        case NasmToken::l_paren:
        {
            clang::SourceLocation lparen_loc = ConsumeParen();
            if (!ParseExpr(e, type))
                return false;
            MatchRHSPunctuation(NasmToken::r_paren, lparen_loc);
            return true;
        }
        case NasmToken::numeric_constant:
        {
            NasmNumericParser num(m_token.getLiteral(), m_token.getLocation(),
                                  m_preproc);
            if (num.hadError())
                e = IntNum(0);
            else if (num.isInteger())
            {
                IntNum val;
                num.getIntegerValue(&val);
                e = val;
            }
            else if (num.isFloat())
            {
                Diag(m_token, diag::err_float_in_directive);
                e = IntNum(0);
            }
            break;
        }
        case NasmToken::identifier:
        {
            IdentifierInfo* ii = m_token.getIdentifierInfo();
            // Might be a register; handle that first.
            ii->DoRegLookup(*m_arch, m_token.getLocation(),
                            m_preproc.getDiagnostics());
            if (const Register* reg = ii->getRegister())
            {
                e = *reg;
                break;
            }
            // Otherwise it must be a symbol; fall through.
            /*@fallthrough@*/
        }
        case NasmToken::label:
        {
            // Use cached symbol if available.
            // We don't try to resolve local labels, etc.
            IdentifierInfo* ii = m_token.getIdentifierInfo();
            SymbolRef sym(0);
            if (ii->isSymbol())
                sym = ii->getSymbol();
            else
            {
                sym = m_object->getSymbol(ii->getName());
                ii->setSymbol(sym);
            }
            sym->Use(m_token.getLocation());
            e = sym;
            break;
        }
        default:
            return false;
        }
    }
    else switch (m_token.getKind())
    {
        case NasmToken::plus:
            ConsumeToken();
            return ParseExpr6(e, type);
        case NasmToken::minus:
            ConsumeToken();
            if (!ParseExpr6(e, type))
                return false;
            e.Calc(Op::NEG);
            return true;
        case NasmToken::tilde:
            ConsumeToken();
            if (!ParseExpr6(e, type))
                return false;
            e.Calc(Op::NOT);
            return true;
        case NasmToken::kw_seg:
            ConsumeToken();
            if (!ParseExpr6(e, type))
                return false;
            e.Calc(Op::SEG);
            return true;
        case NasmToken::l_paren:
        {
            clang::SourceLocation lparen_loc = ConsumeParen();
            if (!ParseExpr(e, type))
                return false;
            MatchRHSPunctuation(NasmToken::r_paren, lparen_loc);
            return true;
        }
        case NasmToken::numeric_constant:
        {
            NasmNumericParser num(m_token.getLiteral(), m_token.getLocation(),
                                  m_preproc);
            if (num.hadError())
                e = IntNum(0);
            else if (num.isInteger())
            {
                IntNum val;
                num.getIntegerValue(&val);
                e = val;
            }
            else if (num.isFloat())
            {
                // FIXME: Make arch-dependent
                e = Expr(std::auto_ptr<llvm::APFloat>(new llvm::APFloat(
                    num.getFloatValue(llvm::APFloat::x87DoubleExtended))));
            }
            break;
        }
        case NasmToken::string_literal:
        {
            NasmStringParser str(m_token.getLiteral(), m_token.getLocation(),
                                 m_preproc);
            if (str.hadError())
                e = IntNum(0);
            else
            {
                IntNum val;
                str.getIntegerValue(&val);
                e = val;
            }
            break;
        }
        case NasmToken::identifier:
        {
            IdentifierInfo* ii = m_token.getIdentifierInfo();
            // Might be a register; handle that first.
            ii->DoRegLookup(*m_arch, m_token.getLocation(),
                            m_preproc.getDiagnostics());
            if (const Register* reg = ii->getRegister())
            {
                if (type == DV_EXPR)
                    Diag(m_token, diag::err_data_value_register);
                e = *reg;
                break;
            }
            // Might be an unrecognized keyword.
            if (CheckKeyword(ii))
                return ParseExpr6(e, type); // recognized, reparse
            /*@fallthrough@*/
        }
        case NasmToken::label:
        {
            IdentifierInfo* ii = m_token.getIdentifierInfo();
            SymbolRef sym = ParseSymbol(ii);
            sym->Use(m_token.getLocation());
            e = sym;
            break;
        }
        case NasmToken::dollar:
            // "$" references the current assembly position
            if (!m_abspos.isEmpty())
                e = m_abspos;
            else
            {
                SymbolRef sym = m_object->AddNonTableSymbol("$");
                m_bc = &m_container->FreshBytecode();
                Location loc = {m_bc, m_bc->getFixedLen()};
                sym->CheckedDefineLabel(loc, m_token.getLocation(),
                                        m_preproc.getDiagnostics());
                e = sym;
            }
            break;
        case NasmToken::dollardollar:
            // "$$" references the start of the current section
            if (!m_absstart.isEmpty())
                e = m_absstart;
            else
            {
                SymbolRef sym = m_object->AddNonTableSymbol("$$");
                Location loc = {&m_container->bytecodes_front(), 0};
                sym->CheckedDefineLabel(loc, m_token.getLocation(),
                                        m_preproc.getDiagnostics());
                e = sym;
            }
            break;
        default:
            return false;
    }
    ConsumeToken();
    return true;
}

SymbolRef
NasmParser::ParseSymbol(IdentifierInfo* ii, bool* local)
{
    const char* name = ii->getNameStart();
    unsigned int len = ii->getLength();

    if (local)
        *local = false;

    // see if there's a cached version
    if (ii->isSymbol())
        return ii->getSymbol();

    // skip over initial $ (forced identifier)
    if (name[0] == '$')
        ++name;

    // check for local labels
    if (len > 1 && name[0] == '.')
    {
        // check for special labels like ..start
        if (len > 2 && name[1] == '.')
        {
            // check for non-local ..@label
            if (len > 3 && name[2] == '@')
            {
                SymbolRef sym = m_object->getSymbol(name);
                ii->setSymbol(sym);    // cache it
                return sym;
            }

            // otherwise it's a special symbol; skip the ".." portion
            SymbolRef sym = m_object->FindSpecialSymbol(name+2);
            ii->setSymbol(sym);    // cache it
            return sym;
        }

        if (m_locallabel_base.empty())
            Diag(m_token, diag::warn_no_nonlocal);

        // set local flag if possible
        if (local)
            *local = true;
        // don't try to cache local labels
        return m_object->getSymbol(m_locallabel_base + name);
    }

    // just a normal label
    SymbolRef sym = m_object->getSymbol(name);
    ii->setSymbol(sym);    // cache it
    return sym;
}

void
NasmParser::DefineLabel(SymbolRef sym, clang::SourceLocation source, bool local)
{
    if (!local)
        m_locallabel_base = sym->getName();

    if (!m_abspos.isEmpty())
        sym->CheckedDefineEqu(m_abspos, source, m_preproc.getDiagnostics());
    else
    {
        m_bc = &m_container->FreshBytecode();
        Location loc = {m_bc, m_bc->getFixedLen()};
        sym->CheckedDefineLabel(loc, source, m_preproc.getDiagnostics());
    }
}

void
NasmParser::DirAbsolute(DirectiveInfo& info, Diagnostic& diags)
{
    Object& object = info.getObject();
    m_absstart = info.getNameValues().front().getExpr(object);
    m_abspos = m_absstart;
    object.setCurSection(0);
}

void
NasmParser::DirAlign(DirectiveInfo& info, Diagnostic& diags)
{
    Object& object = info.getObject();
    NameValues& namevals = info.getNameValues();
    clang::SourceLocation source = info.getSource();

    // Really, we shouldn't end up with an align directive in an absolute
    // section (as it's supposed to be only used for nop fill), but handle
    // it gracefully anyway.
    if (!m_abspos.isEmpty())
    {
        Expr e = SUB(m_absstart, m_abspos);
        e &= SUB(namevals.front().getExpr(object), 1);
        m_abspos += e;
    }
    else
    {
        Section* cur_section = object.getCurSection();
        Expr boundval = namevals.front().getExpr(object);

        // Largest .align in the section specifies section alignment.
        // Note: this doesn't match NASM behavior, but is a lot more
        // intelligent!
        boundval.Simplify();
        if (boundval.isIntNum())
        {
            unsigned long boundint = boundval.getIntNum().getUInt();

            // Alignments must be a power of two.
            if (isExp2(boundint))
            {
                if (boundint > cur_section->getAlign())
                    cur_section->setAlign(boundint);
            }
        }

        // As this directive is called only when nop is used as fill, always
        // use arch (nop) fill.
        AppendAlign(*cur_section, boundval, Expr(), Expr(),
                    /*cur_section->isCode() ?*/
                    object.getArch()->getFill()/* : 0*/,
                    source);
    }
}

void
NasmParser::DoDirective(llvm::StringRef name, DirectiveInfo& info)
{
    ++num_directive;
    Directive handler;
    if (m_dirs->get(&handler, name))
        handler(info, m_preproc.getDiagnostics());
    else
    {
        Diag(info.getSource(), diag::err_unrecognized_directive);
        return;
    }
    Section* cursect = m_object->getCurSection();
    if (!m_absstart.isEmpty() && cursect)
    {
        // We switched to a new section.  Get out of absolute section mode.
        m_absstart.Clear();
        m_abspos.Clear();
    }
}
