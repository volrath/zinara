package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.CharType;
import zinara.code_generator.Genx86;
import zinara.exceptions.InvalidCodeException;

import java.io.IOException;

public class CharExp extends Expression {
    public char value;
    public CharExp ( char n ) { value=n; type = new CharType(); }
    public Type getType() { return type; }
    public String toString() { return Character.toString(value); }

    public void tox86(Genx86 generate)
	throws IOException,InvalidCodeException {
	String reg = generate.regName(register,new CharType());
 	generate.write(generate.movChar(reg,generate.toASCII(value)));
    }

    public boolean isStaticallyKnown() { return true; }

    public Object staticValue() { return new Character(value); }
}
