package zinara.ast.expression;
import zinara.code_generator.*;

import zinara.ast.type.Type;
import zinara.ast.type.CharType;

public class CharExp extends Expression {
    public char value;
    public CharExp ( char n ) { value=n; type = new CharType(); }
    public Type getType() { return type; }
    public String toString() { return Character.toString(value); }

    public String tox86(Genx86 generate){
 	return generate.mov(generate.current_reg(),generate.toASCII(value));
    }
}
