package zinara.ast.expression;
import zinara.code_generator.*;

import zinara.ast.type.Type;
import zinara.ast.type.BoolType;

public class TrueExp extends Expression {
    public TrueExp () { type = new BoolType(); }
    public Type getType() { return type; }
    public String toString() { return "True"; }

    public String tox86(Genx86 generate){
        return "";
    }
}
