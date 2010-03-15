package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.BoolType;

public class TrueExp extends Expression {
    public TrueExp () {}
    public Type getType() { return new BoolType(); }
    public String toString() { return "True"; }
}
