package zinara.ast.expression;
import zinara.code_generator.*;

import zinara.ast.type.Type;
import zinara.ast.type.IntType;

public class ReadExp extends Expression {
    public ReadExp () {}
    public Type getType() { return new IntType(); }
    public String toString() { return "READ"; }

    public String tox86(Genx86 generate){
        return "";
    }
}
