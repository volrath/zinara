package zinara.ast.expression;

import zinara.ast.type.basicTypes;

public class IntegerExp extends Expression {
    public int value;
    public IntegerExp ( int n ) { value=n; }
    public int getType() { return basicTypes.Int; }
}
