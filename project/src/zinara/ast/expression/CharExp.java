package zinara.ast.expression;

import zinara.semantic.basicTypes;

public class CharExp extends Expression {
    public char value;
    public CharExp ( char n ) { value=n; }
    public Integer getType() { return basicTypes.Char; }
}
