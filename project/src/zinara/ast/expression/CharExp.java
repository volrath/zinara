package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.CharType;
import zinara.code_generator.Genx86;

import java.io.IOException;

public class CharExp extends Expression {
    public char value;
    public CharExp ( char n ) { value=n; type = new CharType(); }
    public Type getType() { return type; }
    public String toString() { return Character.toString(value); }

    public void tox86(Genx86 generate) throws IOException {
 	generate.write(generate.mov(generate.current_reg(),generate.toASCII(value)));
    }
}
