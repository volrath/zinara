package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.BoolType;

public class FalseExp extends Expression {
    public FalseExp () {}
    public Type getType() { return new BoolType(); }
    public String toString() { return "False"; }
}
