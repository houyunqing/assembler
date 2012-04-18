/* eval.c    expression evaluator for the Netwide Assembler
 *
 * The Netwide Assembler is copyright (C) 1996 Simon Tatham and
 * Julian Hall. All rights reserved. The software is
 * redistributable under the licence given in the file "Licence"
 * distributed in the NASM archive.
 *
 * initial version 27/iii/95 by Simon Tatham
 */
#include <cctype>

#include "yasmx/Expr.h"
#include "yasmx/IntNum.h"
#include "yasmx/Object.h"
#include "yasmx/Symbol.h"

#include "nasm.h"
#include "nasmlib.h"
#include "nasm-eval.h"


using yasm::Expr;
using yasm::IntNum;

namespace nasm {

/* The assembler object (for symbol table). */
yasm::Object *yasm_object;

static scanner scan;    /* Address of scanner routine */
static efunc error;     /* Address of error reporting routine */
static curl_eval curly_evaluator; /*curly structure processor func*/
static ppdir_eval ppdir_evaluator;/* %ifdir expression (without the
                                    curly structure) handler */

void setfuncs(scanner sc,efunc errfunc, curl_eval curl_evalfunc, ppdir_eval ppdirfunc)
{
    scan = sc;
    error = errfunc;
    curly_evaluator = curl_evalfunc;
    ppdir_evaluator = ppdirfunc;
}

static struct tokenval *tokval;   /* The current token */
static int i;                     /* The t_type of tokval */

static void *scpriv;

/*
 * Recursive-descent parser. Called with a single boolean operand,
 * which is TRUE if the evaluation is critical (i.e. unresolved
 * symbols are an error condition). Must update the global `i' to
 * reflect the token after the parsed string. May return NULL.
 *
 * evaluate() should report its own errors: on return it is assumed
 * that if NULL has been returned, the error has already been
 * reported.
 */

/*
 * Grammar parsed is:
 *
 * expr  : bexpr [ WRT expr6 ]
 * bexpr : rexpc or expr0 depending on relative-mode setting
 * rexpc : rexp0 [ ? rexp0 : rexp0...]
 * rexp0 : rexp1 [ {||} rexp1...]
 * rexp1 : rexp2 [ {^^} rexp2...]
 * rexp2 : rexp3 [ {&&} rexp3...]
 * rexp3 : expr0 [ {=,==,<>,!=,<,>,<=,>=} expr0 ]
 * expr0 : expr1 [ {|} expr1...]
 * expr1 : expr2 [ {^} expr2...]
 * expr2 : expr3 [ {&} expr3...]
 * expr3 : expr4 [ {<<,>>} expr4...]
 * expr4 : expr5 [ {+,-} expr5...]
 * expr5 : expr6 [ {*,/,%,//,%%} expr6...]
 * expr6 : { ~,+,-,SEG } expr6
 *       | (bexpr)
 *       | symbol
 *       | $
 *       | number
 */

static bool rexpc(Expr*);
static bool rexp0(Expr*), rexp1(Expr*), rexp2(Expr*), rexp3(Expr*);

static bool expr0(Expr*), expr1(Expr*), expr2(Expr*), expr3(Expr*);
static bool expr4(Expr*), expr5(Expr*), expr6(Expr*);

static bool (*bexpr)(Expr*);


/*
 * Added to process the !?: operand.
 * !? is chosen instead of ? because ? can be recognised as a part or
 * the beginning of an identifier in the nasm language.
 */
static bool rexpc(Expr* e)
{
    if (!rexp0(e))
        return false;
    while (i == TOKEN_TERN)
    {
        i = scan(scpriv, tokval);
        Expr f, f2;
        if (!rexp1(&f))
            return false;
        if (i != ':') {
            /*
             * FIXME: when user attempts to use floating point
             * numbers, the dot will be an unrecognised token. If the
             * float comes before :, then the following error line
             * will be reported, which seems inappropriate.
             */
            error(ERR_FATAL, "expecting `:'");
            return false;
        }
        i = scan(scpriv, tokval);
        if (!rexp1(&f2))
            return false;
        /*
         * yasm-nextgen currently has no handler for ternary operators
         * so the e->Calc approach cannot be used here and the stuffs
         * inside e->Calc is directly done here. Might not worth
         * fixing anyway since the ?: is probably the only ternary
         * operator that will be supported by yasm-nextgen
         */
        e->Append(f);
        e->Append(f2);
        e->AppendOp(yasm::Op::COND, 3);

    }
    return true;
}

static bool rexp0(Expr* e)
{
    if (!rexp1(e))
        return false;

    while (i == TOKEN_DBL_OR)
    {
        i = scan(scpriv, tokval);
        Expr f;
        if (!rexp1(&f))
            return false;

        e->Calc(yasm::Op::LOR, f);
    }
    return true;
}

static bool rexp1(Expr* e)
{
    if (!rexp2(e))
        return false;

    while (i == TOKEN_DBL_XOR)
    {
        i = scan(scpriv, tokval);
        Expr f;
        if (!rexp2(&f))
            return false;

        e->Calc(yasm::Op::LXOR, f);
    }
    return true;
}

static bool rexp2(Expr* e)
{
    if (!rexp3(e))
        return false;
    while (i == TOKEN_DBL_AND)
    {
        i = scan(scpriv, tokval);
        Expr f;
        if (!rexp3(&f))
            return false;

        e->Calc(yasm::Op::LAND, f);
    }
    return true;
}

static bool rexp3(Expr* e)
{
    if (!expr0(e))
        return false;

    while (i == TOKEN_EQ || i == TOKEN_LT || i == TOKEN_GT ||
           i == TOKEN_NE || i == TOKEN_LE || i == TOKEN_GE)
    {
        int j = i;
        i = scan(scpriv, tokval);
        Expr f;
        if (!expr0(&f))
            return false;

        switch (j)
        {
            case TOKEN_EQ:
                e->Calc(yasm::Op::EQ, f);
                break;
            case TOKEN_LT:
                e->Calc(yasm::Op::LT, f);
                break;
            case TOKEN_GT:
                e->Calc(yasm::Op::GT, f);
                break;
            case TOKEN_NE:
                e->Calc(yasm::Op::NE, f);
                break;
            case TOKEN_LE:
                e->Calc(yasm::Op::LE, f);
                break;
            case TOKEN_GE:
                e->Calc(yasm::Op::GE, f);
                break;
        }
    }
    return true;
}

static bool expr0(Expr* e)
{
    if (!expr1(e))
        return false;

    while (i == '|')
    {
        i = scan(scpriv, tokval);
        Expr f;
        if (!expr1(&f))
            return false;

        e->Calc(yasm::Op::OR, f);
    }
    return true;
}

static bool expr1(Expr* e)
{
    if (!expr2(e))
        return false;

    while (i == '^') {
        i = scan(scpriv, tokval);
        Expr f;
        if (!expr2(&f))
            return false;

        e->Calc(yasm::Op::XOR, f);
    }
    return true;
}

static bool expr2(Expr* e)
{
    if (!expr3(e))
        return false;

    while (i == '&') {
        i = scan(scpriv, tokval);
        Expr f;
        if (!expr3(&f))
            return false;

        e->Calc(yasm::Op::AND, f);
    }
    return true;
}

static bool expr3(Expr* e)
{
    if (!expr4(e))
        return false;

    while (i == TOKEN_SHL || i == TOKEN_SHR)
    {
        int j = i;
        i = scan(scpriv, tokval);
        Expr f;
        if (!expr4(&f))
            return false;

        switch (j) {
            case TOKEN_SHL:
                e->Calc(yasm::Op::SHL, f);
                break;
            case TOKEN_SHR:
                e->Calc(yasm::Op::SHR, f);
                break;
        }
    }
    return true;
}

static bool expr4(Expr* e)
{
    if (!expr5(e))
        return false;
    while (i == '+' || i == '-')
    {
        int j = i;
        i = scan(scpriv, tokval);
        Expr f;
        if (!expr5(&f))
            return false;
        switch (j) {
          case '+':
            e->Calc(yasm::Op::ADD, f);
            break;
          case '-':
            e->Calc(yasm::Op::SUB, f);
            break;
        }
    }
    return true;
}

static bool expr5(Expr* e)
{
    if (!expr6(e))
        return false;
    while (i == '*' || i == '/' || i == '%' ||
           i == TOKEN_SDIV || i == TOKEN_SMOD)
    {
        int j = i;
        i = scan(scpriv, tokval);
        Expr f;
        if (!expr6(&f))
            return false;
        switch (j) {
          case '*':
            e->Calc(yasm::Op::MUL, f);
            break;
          case '/':
            e->Calc(yasm::Op::DIV, f);
            break;
          case '%':
            e->Calc(yasm::Op::MOD, f);
            break;
          case TOKEN_SDIV:
            e->Calc(yasm::Op::SIGNDIV, f);
            break;
          case TOKEN_SMOD:
            e->Calc(yasm::Op::SIGNMOD, f);
            break;
        }
    }
    return true;
}

static bool expr6(Expr* e)
{
    if (i == '-') {
        i = scan(scpriv, tokval);
        if (!expr6(e))
            return false;
        e->Calc(yasm::Op::NEG);
        return true;
    } else if (i == '+') {
        i = scan(scpriv, tokval);
        return expr6(e);
    } else if (i == '~') {
        i = scan(scpriv, tokval);
        if (!expr6(e))
            return false;
        e->Calc(yasm::Op::NOT);
        return true;
    } else if (i == '!') {
	/*
	 * This LNOT operator isn't a standard part of NASM's
	 * preprocessor expression syntax. Added here to get the work
	 * done.
	 */
        i = scan(scpriv, tokval);
        if (!expr6(e))
            return false;
        e->Calc(yasm::Op::LNOT);
        return true;
    } else if (i == TOKEN_SEG) {
        i = scan(scpriv, tokval);
        if (!expr6(e))
            return false;
        error(ERR_NONFATAL, "%s not supported", "SEG");
        return true;
    } else if (i == '(') {
        i = scan(scpriv, tokval);
        if (!bexpr(e))
            return false;
        if (i != ')') {
            error(ERR_NONFATAL, "expecting `)'");
            return false;
        }
        i = scan(scpriv, tokval);
        return true;
    } else if (i == '{' ) {
        /*
         * scpriv -> A -> B
         * A is the current Token*, B is the current Token
         * curly_evaluator updates A to A2, but also calls
         * if_condition(), which may change the value of scpriv
         * again by calling evaluate(). 
         * Thus when curly_evaluator returns, scpriv would no longer
         * point to A2, but would point, instead, to another Token*
         * scpriv -broken-> A2 -> B2
         *        -newly set-> A3
         * Since A2 is needed for correct behaviour, scpriv must be
         * backed up and restored after curly_evaluator returns, so
         * that it still points to A2
         *
         * A2 is the Token* after the '}' that corresponds to the
         * opening '{'
         */
        void* saved_priv = scpriv;
        tokenval *saved_tok = tokval;
        int j = curly_evaluator(scpriv);
        scpriv = saved_priv;
        tokval = saved_tok;
        if( j == -1)
            return false;
        *e = Expr(IntNum(j));
        i = scan(scpriv, tokval);
        return true;
    }
    else if (i == TOKEN_NUM || i == TOKEN_ID ||
             i == TOKEN_HERE || i == TOKEN_BASE)
    {
        switch (i) {
          case TOKEN_NUM:
            *e = Expr(*tokval->t_integer);
            break;
          case TOKEN_ID:
            if (yasm_object) {
                yasm::SymbolRef sym = yasm_object->getSymbol(tokval->t_charptr);
                if (sym) {
                    sym->Use(yasm::SourceLocation());
                    *e = Expr(sym);
                } else {
                    error(ERR_NONFATAL,
                          "undefined symbol `%s' in preprocessor",
                          tokval->t_charptr);
                    *e = Expr(IntNum(1));
                }
                break;
            }
            /*fallthrough*/
          case TOKEN_HERE:
          case TOKEN_BASE:
            error(ERR_NONFATAL,
                  "cannot reference symbol `%s' in preprocessor",
                  (i == TOKEN_ID ? tokval->t_charptr :
                   i == TOKEN_HERE ? "$" : "$$"));
            *e = Expr(IntNum(1));
            break;
        }
        i = scan(scpriv, tokval);
        return true;
    } 
    else if(i == TOKEN_PPDIR) {
        /* scpriv still points to the %ppdir token because scan() does
         * not consume %ppdir tokens(actually all TOK_PREPROC_IDs are
         * sent in here)
         */
        int j = ppdir_evaluator(scpriv);
        if( j == -1 )
            return false;
        *e = Expr(IntNum(j));
        i = scan(scpriv, tokval);
        return true;
    }
    else {
        error(ERR_NONFATAL, "expression syntax error");
        return false;
    }
}

Expr *nasm_evaluate (void *scprivate, struct tokenval *tv,
                          int critical)
{
    if (critical & CRITICAL) {
        critical &= ~CRITICAL;
        bexpr = rexpc;
    } else
        bexpr = expr0;

    scpriv = scprivate;
    tokval = tv;

    if (tokval->t_type == TOKEN_INVALID)
        i = scan(scpriv, tokval);
    else
        i = tokval->t_type;

    Expr* e = new Expr;
    if (bexpr(e))
        return e;
    delete e;
    return NULL;
}

} // namespace nasm
