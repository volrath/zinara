package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.IntType;

public class ReadExp extends Expression {
    public ReadExp () {}
    public Type getType() { return new IntType(); }
    public String toString() { return "READ"; }
}
