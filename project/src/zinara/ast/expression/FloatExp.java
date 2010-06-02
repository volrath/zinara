package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.FloatType;
import zinara.code_generator.Genx86;

import java.io.IOException;

public class FloatExp extends Expression {
    public float value;
    public FloatExp ( float n ) { value=n; type = new FloatType(); }
    public Type getType() { return type; }
    public String toString() { return Float.toString(value); }

    public void tox86(Genx86 generate) throws IOException {
 	generate.write(generate.movReal(generate.regName(register),generate.toReal(value)));
    }

    public boolean isStaticallyKnown() { return true; }
}
