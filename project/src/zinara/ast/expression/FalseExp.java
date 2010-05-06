package zinara.ast.expression;
import zinara.code_generator.*;

import zinara.ast.type.Type;
import zinara.ast.type.BoolType;

public class FalseExp extends Expression {
    public FalseExp () {}
    public Type getType() { return new BoolType(); }
    public String toString() { return "False"; }

    public String tox86(Genx86 generate){
        return "";
    }
}
