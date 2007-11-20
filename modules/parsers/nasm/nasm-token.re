//
// NASM-compatible re2c lexer
//
//  Copyright (C) 2001-2007  Peter Johnson
//
//  Portions based on re2c's example code.
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
#include <util.h>

#include <libyasm/arch.h>
#include <libyasm/compose.h>
#include <libyasm/errwarn.h>
#include <libyasm/nocase.h>
#include <libyasm/object.h>

#include "modules/parsers/nasm/nasm-parser.h"


namespace yasm { namespace parser { namespace nasm {

#define BSIZE   8192

#define YYCURSOR        cursor
#define YYLIMIT         (m_s.lim)
#define YYMARKER        (m_s.ptr)
#define YYFILL(n)       {fill(cursor);}

#define RETURN(i)       {m_s.cur = cursor; m_tokch = m_s.tok[0]; return i;}

#define SCANINIT()      {m_s.tok = cursor;}

#define TOK             ((char *)m_s.tok)
#define TOKLEN          (size_t)(cursor-m_s.tok)


inline size_t
NasmParser::fill_input(unsigned char* buf, size_t max)
{
    m_is->read((char*)buf, max);
    return m_is->gcount();
}

void
NasmParser::fill(YYCTYPE* &cursor)
{
    if (m_s.fill_helper(cursor, BIND::bind(&NasmParser::fill_input, this, _1, _2))
        && m_save_input) {
        m_save_last ^= 1;
        YYCTYPE* saveline = m_save_line[m_save_last];
        // save next line into cur_line
        int i;
        for (i=0; i<79 && &m_s.tok[i] < m_s.lim && m_s.tok[i] != '\n'; i++)
            saveline[i] = m_s.tok[i];
        saveline[i] = '\0';
    }
}

YYCTYPE *
NasmParser::save_line(YYCTYPE* cursor)
{
    m_save_last ^= 1;
    YYCTYPE* saveline = m_save_line[m_save_last];

    // save next line into cur_line
    if ((YYLIMIT - YYCURSOR) < 80)
        YYFILL(80);
    int i;
    for (i=0; i<79 && &cursor[i] < m_s.lim && cursor[i] != '\n'; i++)
        saveline[i] = cursor[i];
    saveline[i] = '\0';
    return cursor;
}

// starting size of string buffer
#define STRBUF_ALLOC_SIZE       128

static int linechg_numcount;

/*!re2c
  any = [\000-\377];
  digit = [0-9];
  iletter = [a-zA-Z];
  bindigit = [01];
  octdigit = [0-7];
  hexdigit = [0-9a-fA-F];
  ws = [ \t\r];
  quot = ["'];
*/


int
NasmParser::lex(YYSTYPE* lvalp)
{
    YYCTYPE* cursor = m_s.cur;
    YYCTYPE endch;
    YYCTYPE savech;

    // Handle one token of lookahead
    if (m_peek_token != NONE) {
        int tok = m_peek_token;
        *lvalp = m_peek_tokval;     // structure copy
        m_tokch = m_peek_tokch;
        m_peek_token = NONE;
        return tok;
    }

    // Catch EOF
    if (m_s.eof && cursor == m_s.eof)
        return 0;

    // Jump to proper "exclusive" states
    switch (m_state) {
        case DIRECTIVE:
            goto directive;
        case SECTION_DIRECTIVE:
            goto section_directive;
        case DIRECTIVE2:
            goto directive2;
        case LINECHG:
            goto linechg;
        case LINECHG2:
            goto linechg2;
        default:
            break;
    }

scan:
    SCANINIT();

    /*!re2c
        /* standard decimal integer */
        digit+ {
            savech = m_s.tok[TOKLEN];
            m_s.tok[TOKLEN] = '\0';
            lvalp->intn.reset(new IntNum(TOK, 10));
            m_s.tok[TOKLEN] = savech;
            RETURN(INTNUM);
        }
        /* 10010011b - binary number */

        bindigit+ 'b' {
            m_s.tok[TOKLEN-1] = '\0'; /* strip off 'b' */
            lvalp->intn.reset(new IntNum(TOK, 2));
            RETURN(INTNUM);
        }

        /* 777q or 777o - octal number */
        octdigit+ [qQoO] {
            m_s.tok[TOKLEN-1] = '\0'; /* strip off 'q' or 'o' */
            lvalp->intn.reset(new IntNum(TOK, 8));
            RETURN(INTNUM);
        }

        /* 0AAh form of hexidecimal number */
        digit hexdigit* 'h' {
            m_s.tok[TOKLEN-1] = '\0'; /* strip off 'h' */
            lvalp->intn.reset(new IntNum(TOK, 16));
            RETURN(INTNUM);
        }

        /* $0AA and 0xAA forms of hexidecimal number */
        (("$" digit) | "0x") hexdigit+ {
            savech = m_s.tok[TOKLEN];
            m_s.tok[TOKLEN] = '\0';
            if (m_s.tok[1] == 'x')
                /* skip 0 and x */
                lvalp->intn.reset(new IntNum(TOK+2, 16));
            else
                /* don't skip 0 */
                lvalp->intn.reset(new IntNum(TOK+1, 16));
            m_s.tok[TOKLEN] = savech;
            RETURN(INTNUM);
        }

        /* floating point value */
        digit+ "." digit* ('e' [-+]? digit+)? {
            savech = m_s.tok[TOKLEN];
            m_s.tok[TOKLEN] = '\0';
            lvalp->flt.reset(new FloatNum(TOK));
            m_s.tok[TOKLEN] = savech;
            RETURN(FLTNUM);
        }

        /* string/character constant values */
        quot {
            endch = m_s.tok[0];
            goto stringconst;
        }

        /* %line linenum+lineinc filename */
        "%line" {
            m_state = LINECHG;
            linechg_numcount = 0;
            RETURN(LINE);
        }

        /* size specifiers */
        'byte'          { lvalp->int_info = 8; RETURN(SIZE_OVERRIDE); }
        'hword'         {
            lvalp->int_info = m_wordsize/2;
            RETURN(SIZE_OVERRIDE);
        }
        'word'          {
            lvalp->int_info = m_wordsize;
            RETURN(SIZE_OVERRIDE);
        }
        'dword' | 'long'        {
            lvalp->int_info = m_wordsize*2;
            RETURN(SIZE_OVERRIDE);
        }
        'qword'         {
            lvalp->int_info = m_wordsize*4;
            RETURN(SIZE_OVERRIDE);
        }
        'tword'         { lvalp->int_info = 80; RETURN(SIZE_OVERRIDE); }
        'dqword'        {
            lvalp->int_info = m_wordsize*8;
            RETURN(SIZE_OVERRIDE);
        }
        'oword'        {
            lvalp->int_info = m_wordsize*8;
            RETURN(SIZE_OVERRIDE);
        }

        /* pseudo-instructions */
        'db'            { lvalp->int_info = 8; RETURN(DECLARE_DATA); }
        'dhw'           {
            lvalp->int_info = m_wordsize/2;
            RETURN(DECLARE_DATA);
        }
        'dw'            {
            lvalp->int_info = m_wordsize;
            RETURN(DECLARE_DATA);
        }
        'dd'            {
            lvalp->int_info = m_wordsize*2;
            RETURN(DECLARE_DATA);
        }
        'dq'            {
            lvalp->int_info = m_wordsize*4;
            RETURN(DECLARE_DATA);
        }
        'dt'            { lvalp->int_info = 80; RETURN(DECLARE_DATA); }
        'ddq'           {
            lvalp->int_info = m_wordsize*8;
            RETURN(DECLARE_DATA);
        }
        'do'           {
            lvalp->int_info = m_wordsize*8;
            RETURN(DECLARE_DATA);
        }

        'resb'          { lvalp->int_info = 8; RETURN(RESERVE_SPACE); }
        'reshw'         {
            lvalp->int_info = m_wordsize/2;
            RETURN(RESERVE_SPACE);
        }
        'resw'          {
            lvalp->int_info = m_wordsize;
            RETURN(RESERVE_SPACE);
        }
        'resd'          {
            lvalp->int_info = m_wordsize*2;
            RETURN(RESERVE_SPACE);
        }
        'resq'          {
            lvalp->int_info = m_wordsize*4;
            RETURN(RESERVE_SPACE);
        }
        'rest'          { lvalp->int_info = 80; RETURN(RESERVE_SPACE); }
        'resdq'         {
            lvalp->int_info = m_wordsize*8;
            RETURN(RESERVE_SPACE);
        }
        'reso'         {
            lvalp->int_info = m_wordsize*8;
            RETURN(RESERVE_SPACE);
        }

        'incbin'        { RETURN(INCBIN); }

        'equ'           { RETURN(EQU); }

        'times'         { RETURN(TIMES); }

        'seg'           { RETURN(SEG); }
        'wrt'           { RETURN(WRT); }

        'abs'           { RETURN(ABS); }
        'rel'           { RETURN(REL); }

        'nosplit'       { RETURN(NOSPLIT); }
        'strict'        { RETURN(STRICT); }

        /* operators */
        "<<"                    { RETURN(LEFT_OP); }
        ">>"                    { RETURN(RIGHT_OP); }
        "//"                    { RETURN(SIGNDIV); }
        "%%"                    { RETURN(SIGNMOD); }
        "$$"                    { RETURN(START_SECTION_ID); }
        [-+|^*&/%~$():=,\[]     { RETURN(m_s.tok[0]); }
        "]"                     { RETURN(m_s.tok[0]); }

        /* special non-local ..@label and labels like ..start */
        ".." [a-zA-Z0-9_$#@~.?]+ {
            lvalp->str.assign(TOK, TOKLEN);
            RETURN(SPECIAL_ID);
        }

        /* local label (.label) */
        "." [a-zA-Z0-9_$#@~?][a-zA-Z0-9_$#@~.?]* {
            if (m_locallabel_base.empty()) {
                lvalp->str.assign(TOK, TOKLEN);
                warn_set(WARN_GENERAL, String::compose(
                    N_("no non-local label before `%1'"), lvalp->str));
            } else {
                lvalp->str = m_locallabel_base;
                lvalp->str.append(TOK, TOKLEN);
            }

            RETURN(LOCAL_ID);
        }

        /* forced identifier */
        "$" [a-zA-Z0-9_$#@~.?]+ {
            lvalp->str.assign(TOK+1, TOKLEN-1);
            RETURN(ID);
        }

        /* identifier that may be a register, instruction, etc. */
        [a-zA-Z_?][a-zA-Z0-9_$#@~.?]* {
            savech = m_s.tok[TOKLEN];
            m_s.tok[TOKLEN] = '\0';
            if (m_state != INSTRUCTION) {
                Arch::InsnPrefix ip =
                    m_arch->parse_check_insnprefix(TOK, TOKLEN, get_cur_line());
                m_s.tok[TOKLEN] = savech;
                switch (ip.get_type()) {
                    case Arch::InsnPrefix::INSN:
                        lvalp->bc = ip.release_insn();
                        m_state = INSTRUCTION;
                        RETURN(INSN);
                    case Arch::InsnPrefix::PREFIX:
                        lvalp->prefix = ip.get_prefix();
                        RETURN(PREFIX);
                    default:
                        break;
                }
            }
            Arch::RegTmod regtmod = m_arch->parse_check_regtmod(TOK, TOKLEN);
            m_s.tok[TOKLEN] = savech;
            switch (regtmod.get_type()) {
                case Arch::RegTmod::REG:
                    lvalp->reg = regtmod.get_reg();
                    RETURN(REG);
                case Arch::RegTmod::SEGREG:
                    lvalp->segreg = regtmod.get_segreg();
                    RETURN(SEGREG);
                case Arch::RegTmod::TARGETMOD:
                    lvalp->targetmod = regtmod.get_tmod();
                    RETURN(TARGETMOD);
                default:
                    break;
            }
            /* Propagate errors in case we got a warning from the arch */
            m_errwarns->propagate(get_cur_line());
            /* Just an identifier, return as such. */
            lvalp->str.assign(TOK, TOKLEN);
            RETURN(ID);
        }

        ";" (any \ [\n])*       { goto scan; }

        ws+                     { goto scan; }

        "\n"                    {
            if (m_save_input)
                cursor = save_line(cursor);
            m_state = INITIAL;
            RETURN(m_s.tok[0]);
        }

        any {
            warn_set(WARN_UNREC_CHAR, String::compose(
                N_("ignoring unrecognized character `%1'"),
                conv_unprint(m_s.tok[0])));
            goto scan;
        }
    */

    // %line linenum+lineinc filename
linechg:
    SCANINIT();

    /*!re2c
        digit+ {
            linechg_numcount++;
            savech = m_s.tok[TOKLEN];
            m_s.tok[TOKLEN] = '\0';
            lvalp->intn.reset(new IntNum(TOK, 10));
            m_s.tok[TOKLEN] = savech;
            RETURN(INTNUM);
        }

        "\n" {
            if (m_save_input)
                cursor = save_line(cursor);
            m_state = INITIAL;
            RETURN(m_s.tok[0]);
        }

        "+" {
            RETURN(m_s.tok[0]);
        }

        ws+ {
            if (linechg_numcount == 2) {
                m_state = LINECHG2;
                goto linechg2;
            }
            goto linechg;
        }

        any {
            warn_set(WARN_UNREC_CHAR, String::compose(
                N_("ignoring unrecognized character `%1'"),
                conv_unprint(m_s.tok[0])));
            goto linechg;
        }
    */

linechg2:
    SCANINIT();

    /*!re2c
        "\n" {
            if (m_save_input)
                cursor = save_line(cursor);
            m_state = INITIAL;
            RETURN(m_s.tok[0]);
        }

        "\r" { }

        (any \ [\r\n])+ {
            m_state = LINECHG;
            lvalp->str.assign(TOK, TOKLEN);
            RETURN(FILENAME);
        }
    */

    // directive: [name value]
directive:
    SCANINIT();

    /*!re2c
        [\]\n] {
            if (m_save_input)
                cursor = save_line(cursor);
            m_state = INITIAL;
            RETURN(m_s.tok[0]);
        }

        [a-zA-Z_][a-zA-Z_0-9]* {
            lvalp->str.assign(TOK, TOKLEN);
            if (String::nocase_equal(lvalp->str, "section") ||
                String::nocase_equal(lvalp->str, "segment"))
                m_state = SECTION_DIRECTIVE;
            else
                m_state = DIRECTIVE2;
            RETURN(DIRECTIVE_NAME);
        }

        any {
            warn_set(WARN_UNREC_CHAR, String::compose(
                N_("ignoring unrecognized character `%1'"),
                conv_unprint(m_s.tok[0])));
            goto directive;
        }
    */

    // section directive (the section name portion thereof)
section_directive:
    SCANINIT();

    /*!re2c
        [a-zA-Z0-9_$#@~.?-]+ {
            lvalp->str.assign(TOK, TOKLEN);
            m_state = DIRECTIVE2;
            RETURN(STRING);
        }

        quot            {
            m_state = DIRECTIVE2;
            endch = m_s.tok[0];
            goto stringconst;
        }

        ws+             {
            m_state = DIRECTIVE2;
            goto section_directive;
        }

        "]" {
            m_state = INITIAL;
            RETURN(m_s.tok[0]);
        }

        "\n"                    {
            if (m_save_input)
                cursor = save_line(cursor);
            m_state = INITIAL;
            RETURN(m_s.tok[0]);
        }

        any {
            warn_set(WARN_UNREC_CHAR, String::compose(
                N_("ignoring unrecognized character `%1'"),
                conv_unprint(m_s.tok[0])));
            goto section_directive;
        }
    */

    // inner part of directive
directive2:
    SCANINIT();

    /*!re2c
        /* standard decimal integer */
        digit+ {
            savech = m_s.tok[TOKLEN];
            m_s.tok[TOKLEN] = '\0';
            lvalp->intn.reset(new IntNum(TOK, 10));
            m_s.tok[TOKLEN] = savech;
            RETURN(INTNUM);
        }
        /* 10010011b - binary number */

        bindigit+ 'b' {
            m_s.tok[TOKLEN-1] = '\0'; /* strip off 'b' */
            lvalp->intn.reset(new IntNum(TOK, 2));
            RETURN(INTNUM);
        }

        /* 777q or 777o - octal number */
        octdigit+ [qQoO] {
            m_s.tok[TOKLEN-1] = '\0'; /* strip off 'q' or 'o' */
            lvalp->intn.reset(new IntNum(TOK, 8));
            RETURN(INTNUM);
        }

        /* 0AAh form of hexidecimal number */
        digit hexdigit* 'h' {
            m_s.tok[TOKLEN-1] = '\0'; /* strip off 'h' */
            lvalp->intn.reset(new IntNum(TOK, 16));
            RETURN(INTNUM);
        }

        /* $0AA and 0xAA forms of hexidecimal number */
        (("$" digit) | "0x") hexdigit+ {
            savech = m_s.tok[TOKLEN];
            m_s.tok[TOKLEN] = '\0';
            if (m_s.tok[1] == 'x')
                /* skip 0 and x */
                lvalp->intn.reset(new IntNum(TOK+2, 16));
            else
                /* don't skip 0 */
                lvalp->intn.reset(new IntNum(TOK+1, 16));
            m_s.tok[TOKLEN] = savech;
            RETURN(INTNUM);
        }

        /* string/character constant values */
        quot {
            endch = m_s.tok[0];
            goto stringconst;
        }

        /* operators */
        "<<"                    { RETURN(LEFT_OP); }
        ">>"                    { RETURN(RIGHT_OP); }
        "//"                    { RETURN(SIGNDIV); }
        "%%"                    { RETURN(SIGNMOD); }
        [-+|^*&/%~$():=,\[]     { RETURN(m_s.tok[0]); }

        /* handle ] for directives */
        "]" {
            m_state = INITIAL;
            RETURN(m_s.tok[0]);
        }

        /* forced identifier; within directive, don't strip '$', this is
         * handled later.
         */
        "$" [a-zA-Z0-9_$#@~.?]+ {
            lvalp->str.assign(TOK, TOKLEN);
            RETURN(ID);
        }

        /* identifier; within directive, no local label mechanism */
        [a-zA-Z_.?][a-zA-Z0-9_$#@~.?]* {
            savech = m_s.tok[TOKLEN];
            m_s.tok[TOKLEN] = '\0';
            Arch::RegTmod regtmod = m_arch->parse_check_regtmod(TOK, TOKLEN);
            m_s.tok[TOKLEN] = savech;
            lvalp->reg = regtmod.get_reg();
            if (lvalp->reg)
                RETURN(REG);
            // Propagate errors in case we got a warning from the arch
            m_errwarns->propagate(get_cur_line());
            /* Just an identifier, return as such. */
            lvalp->str.assign(TOK, TOKLEN);
            RETURN(ID);
        }

        ";" (any \ [\n])*       { goto directive2; }

        ws+                     { goto directive2; }

        "\n"                    {
            if (m_save_input)
                cursor = save_line(cursor);
            m_state = INITIAL;
            RETURN(m_s.tok[0]);
        }

        any {
            warn_set(WARN_UNREC_CHAR, String::compose(
                N_("ignoring unrecognized character `%1'"),
                conv_unprint(m_s.tok[0])));
            goto scan;
        }
     */

    // string/character constant values
stringconst:
    lvalp->str.clear();

stringconst_scan:
    SCANINIT();

    /*!re2c
        "\n"    {
            if (m_save_input)
                cursor = save_line(cursor);

            if (cursor == m_s.eof)
                throw SyntaxError(N_("unexpected end of file in string"));
            else
                throw SyntaxError(N_("unterminated string"));
        }

        any     {
            if (m_s.tok[0] == endch)
                RETURN(STRING);
            lvalp->str += m_s.tok[0];
            goto stringconst_scan;
        }
    */
}

}}} // namespace yasm::parser::nasm