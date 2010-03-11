package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.CharType;

public class CharExp extends Expression {
    public char value;
    public CharExp ( char n ) { value=n; }
    public Type getType() { return new CharType(); }
}
