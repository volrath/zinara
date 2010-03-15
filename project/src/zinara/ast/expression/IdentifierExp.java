package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.IntType;

public class IdentifierExp extends Expression {
    public String value;

    public IdentifierExp (String n) { value=n; }
    public Type getType() { return new IntType(); }
    public String toString() { return value; }
}

