#include <iostream>

#include <libyasm/intnum.h>
#include <libyasm/expr.h>

using namespace yasm;

int
main()
{
    Expr::Ptr e(new Expr(new IntNum(5)));
#if 0
    Expr *e2 = new Expr(Expr::NEG, new IntNum(5));
    Expr *e3 = new Expr(e2, Expr::MUL, new IntNum(6));
    Expr *e4 = new Expr(e, Expr::ADD, e3);
#else
    Expr::Ptr e2(new Expr(Op::NEG, new IntNum(5)));
    Expr::Ptr e3(new Expr(e2, Op::MUL, new IntNum(6)));
    Expr::Ptr e4(new Expr(e, Op::ADD, e3));
#endif

    std::cout << *e4 << std::endl;

    e4->simplify();

    std::cout << *e4 << std::endl;

#if 0
    delete e4;
#endif

    return 0;
}
