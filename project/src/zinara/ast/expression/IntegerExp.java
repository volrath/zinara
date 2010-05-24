package zinara.ast.expression;
import zinara.code_generator.*;

import zinara.ast.type.Type;
import zinara.ast.type.IntType;

public class IntegerExp extends Expression {
    private int value;
    public IntegerExp ( int n ) { value=n; type = new IntType(); }
    public int getValue() { return value; }
    public Type getType() { return type; }
    public String toString() { return Integer.toString(value); }

    public String tox86(Genx86 generate){
 	return generate.mov(generate.current_reg(),this.toString());	
    }
}
