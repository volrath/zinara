package zinara.ast.expression;

import zinara.semantic.basicTypes;

public class IntegerExp extends Expression {
    public int value;
    public IntegerExp ( int n ) { value=n; }
    public Integer getType() { return basicTypes.Int; }
}
