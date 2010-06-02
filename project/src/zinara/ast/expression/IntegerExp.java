package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.IntType;
import zinara.code_generator.Genx86;

import java.io.IOException;

public class IntegerExp extends Expression {
    private int value;
    public IntegerExp ( int n ) { value=n; type = new IntType(); }
    public int getValue() { return value; }
    public Type getType() { return type; }
    public String toString() { return Integer.toString(value); }

    public void tox86(Genx86 generate) throws IOException {
 	generate.write(generate.movInt(generate.regName(register),this.toString()));
    }

    public boolean isStaticallyKnown() { return true; }

    public Object staticValue() { return null; };
}
