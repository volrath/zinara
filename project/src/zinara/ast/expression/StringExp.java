package zinara.ast.expression;
import zinara.code_generator.*;

import zinara.ast.type.StringType;
import zinara.ast.type.Type;

public class StringExp extends Expression {
    public String value;
    public StringExp(String v) { value = v; }
    public Type getType() { return new StringType(); }
    public String toString() { return "\"" + value + "\""; }

    public String tox86(Genx86 generate){
        return "";
    }
}
