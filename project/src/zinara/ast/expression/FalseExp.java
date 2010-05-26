package zinara.ast.expression;
import zinara.code_generator.*;

import zinara.ast.type.Type;
import zinara.ast.type.BoolType;

public class FalseExp extends Expression {
    public FalseExp () { type = new BoolType(); }
    public Type getType() { return type; }
    public String toString() { return "False"; }

    public void tox86(Genx86 generate){
    }
}
