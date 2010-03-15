package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.IntType;

public class IntegerExp extends Expression {
    public int value;
    public IntegerExp ( int n ) { value=n; }
    public Type getType() { return new IntType(); }
    public String toString() { return Integer.toString(value); }
}
