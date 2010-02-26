package zinara.ast.expression;

import zinara.ast.type.basicTypes;

public class CharExp extends Expression {
    public char value;
    public CharExp ( char n ) { value=n; }
    public int getType() { return basicTypes.Char; }
}
