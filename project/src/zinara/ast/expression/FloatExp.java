package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.FloatType;
import zinara.code_generator.Genx86;

public class FloatExp extends Expression {
    public float value;
    public FloatExp ( float n ) { value=n; }
    public Type getType() { return new FloatType(); }
    public String toString() { return Float.toString(value); }

    public String tox86(Genx86 generate){
 	return generate.mov(generate.current_reg(),generate.toReal(value));	
    }
}
