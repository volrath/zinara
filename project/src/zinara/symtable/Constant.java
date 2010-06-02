package zinara.symtable;

import zinara.ast.expression.Expression;

public class Constant extends Status {
    private Expression expr;

    public Constant(Expression e) { expr = e; }
    public Expression getExpression() { return expr; }
    public String toString() { return "Constant(=" + expr + ")"; }
}
