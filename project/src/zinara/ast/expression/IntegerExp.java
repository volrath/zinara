package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.IntType;
import zinara.code_generator.Genx86;
import zinara.exceptions.InvalidCodeException;

import java.io.IOException;

public class IntegerExp extends Expression {
    private int value;
    public IntegerExp ( int n ) { value=n; type = new IntType(); }
    public int getValue() { return value; }
    public Type getType() { return type; }
    public String toString() { return Integer.toString(value); }

    public void tox86(Genx86 generate) throws IOException,InvalidCodeException {
	String reg = generate.regName(register,new IntType());
 	generate.write(generate.movInt(reg,this.toString()));
    }
}
