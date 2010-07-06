package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.FloatType;
import zinara.code_generator.Genx86;
import zinara.exceptions.InvalidCodeException;

import java.io.IOException;

public class FloatExp extends Expression {
    public float value;
    public FloatExp ( float n ) { value=n; type = new FloatType(); }
    public Type getType() { return type; }
    public String toString() { return Float.toString(value); }

    public void tox86(Genx86 generate) throws IOException,InvalidCodeException {
	String reg = generate.regName(register,new FloatType());
 	generate.write(generate.movReal(reg,generate.toReal(value)));
    }

    public void negative(){ this.value *= -1; }

    public boolean isStaticallyKnown() { return true; }

    public Object staticValue() { return new Float(value); };
}
